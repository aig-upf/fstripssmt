import itertools
import copy

from collections import defaultdict
from tarski import Term
from tarski.fstrips.representation import substitute_expression
from tarski.syntax.ops import compute_sort_id_assignment

from fstripssmt.solvers.common import solve
from .solvers.pysmt import PySMTTranslator
from .errors import TransformationError

import tarski
from tarski.theories import Theory
from tarski.syntax.ops import free_variables
from tarski.utils import resources
from tarski.syntax import top
from tarski.syntax import symref, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Contradiction, land, lor, implies, exists, Constant, Variable, Predicate, sorts
from tarski.syntax.formulas import quantified, neg, equiv
from tarski.syntax.sorts import parent, Interval
from tarski.syntax.util import get_symbols
import tarski.fstrips as fs


class SemanticInterferences:
    """
    This class implements the computation of semantic interferences using
    various calls to an external SMT solver, a-la:
      Bofill, Miquel, Joan Espasa, and Mateu Villaret.
      Relaxing non-interference requirements in parallel plans.
      Logic Journal of the IGPL (2019).
    """

    def __init__(self, problem, static_symbols):
        super().__init__()
        self.problem = problem
        self.static_symbols = static_symbols
        self.sort_map = dict()  # A map from sorts in the original language to sorts in the metalanguage
        self.metalang = self.setup_metalang(problem)
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.metalang)

        # Map of lifted interferences
        self.interferences = defaultdict(set)
        self.make_useless_checks = True

    def setup_metalang(self, problem):
        """ Set up the Tarski metalanguage where we will build the SMT compilation. """
        lang = problem.language
        theories = lang.theories | {Theory.EQUALITY, Theory.ARITHMETIC}
        ml = tarski.fstrips.language(f"{lang.name}-smt", theories=theories)

        # Declare all sorts
        for s in lang.sorts:
            if not s.builtin and s.name != "object":
                if isinstance(s, Interval):
                    self.sort_map[s] = ml.interval(s.name, parent(s).name, s.lower_bound, s.upper_bound)
                else:
                    self.sort_map[s] = ml.sort(s.name, parent(s).name)

        # Map remaining sorts
        self.sort_map[lang.Object] = ml.Object

        if Theory.ARITHMETIC in lang.theories:
            self.sort_map[lang.Integer] = ml.Integer
            self.sort_map[lang.Natural] = ml.Natural
            self.sort_map[lang.Real] = ml.Real

        if Theory.SETS in lang.theories:
            self.sort_map[sorts.Set(lang, lang.Object)] = sorts.Set(ml, ml.Object)
            self.sort_map[sorts.Set(lang, lang.Integer)] = sorts.Set(ml, ml.Integer)

        # Declare an extra "timestep" sort with a large range, which we'll adjust once we know the horizon
        ml.Timestep = ml.interval("timestep", ml.Natural, 0, 99999)

        # Declare all objects in the metalanguage
        for o in lang.constants():
            ml.constant(o.symbol, o.sort.name)

        # Declare all symbols
        for s in get_symbols(lang, type_="all", include_builtin=False):
            timestep_argument = [_get_timestep_sort(ml)] if self.symbol_is_fluent(s) else []
            if isinstance(s, Predicate):
                sort = [t.name for t in s.sort] + timestep_argument
                ml.predicate(s.name, *sort)
            else:
                sort = [t.name for t in s.domain] + timestep_argument + [s.codomain.name]
                ml.function(s.name, *sort)

        # Declare extra function symbols for the actions
        for a in problem.actions.values():
            sort = [x.sort.name for x in a.parameters] + [_get_timestep_sort(ml)]
            ml.predicate(a.name, *sort)

        return ml

    def to_metalang(self, phi, t, subt=None):
        ml = self.metalang
        subt = t if subt is None else subt

        if isinstance(phi, QuantifiedFormula):
            vs = [self.to_metalang(v, t) for v in phi.variables]
            subf = self.to_metalang(phi.formula, t)
            return quantified(phi.quantifier, *vs, subf)

        elif isinstance(phi, (Tautology, Contradiction)):
            return phi

        elif isinstance(phi, Variable):
            return ml.variable(phi.symbol, phi.sort.name)

        elif isinstance(phi, Constant):
            # We simply map the constant into the target language constant
            return Constant(phi.name, ml.get_sort(phi.sort.name))

        elif isinstance(phi, CompoundFormula):
            return CompoundFormula(phi.connective, tuple(self.to_metalang(psi, t) for psi in phi.subformulas))

        elif isinstance(phi, CompoundTerm):
            args = tuple(self.to_metalang(psi, subt) for psi in phi.subterms)
            symbol = phi.symbol

            if phi.symbol.builtin:
                op, lhs, rhs = ml.get_operator_matching_arguments(phi.symbol.symbol, *args)
                return op(lhs, rhs)

            if symbol.builtin:
                # op, lhs, rhs = ml.get_operator_matching_arguments(symbol.name, *args)
                return self.metalang.dispatch_operator(symbol.name, *args)

            if self.symbol_is_fluent(symbol):
                args += (_get_timestep_term(ml, t),)

            return CompoundTerm(ml.get_function(symbol.name), args)

        elif isinstance(phi, Atom):
            args = tuple(self.to_metalang(psi, subt) for psi in phi.subterms)
            if self.symbol_is_fluent(phi.symbol):
                args += (_get_timestep_term(ml, t),)

            predicate_sort = tuple(self.sort_map[s] for s in phi.symbol.sort)
            return Atom(ml.get_predicate(phi.symbol.name, signature=predicate_sort), args)

        raise TransformationError(f"Don't know how to transform element or expression '{phi}' to the SMT metalanguage")

    def get_interferences(self):
        """ This method is our 'main', where we implement the logic """
        # TODO In the end what we will have are pairs of actions and a set of equalities for their parameters
        # TODO What we can do is skip some checks if we have a "global" hash of this, so we do not need to
        # TODO repeat those checks (as we are not interested in WHY there is interefernce, only if there is)

        actions = self.problem.actions.values()

        with resources.timing(f"Check Simply commuting", newline=True):
            for idx_a, a in enumerate(actions):
                for idx_b, b in enumerate(actions):
                    # The check for simple commutativity is symmetric,
                    # and therefore we do not need to check a,b and b,a.
                    if idx_b >= idx_a:
                        self.simply_commuting(a, b)

        with resources.timing(f"Check 1", newline=True):
            for a in actions:
                for b in actions:
                    self.check1(a, b)

                # case 2
        with resources.timing(f"Check 2", newline=True):
            for a in actions:
                for b in actions:
                    self.check2(a, b)

        #for key, val in self.interferences.items():
        #    a1, a2 = key
        #    for comb in val:
        #        print(f"{a1} -> {a2} when {comb}")

    def simply_commuting(self, a, b):
        """
        Given action schemas a and b:
        Check in what cases the action schemas are not simply commuting. i.e:
        if not(sigma_a = sigma_b) is T-satisfiable

        TODO: Take into account variables in the quantifiers
        TODO: Look more closely what happens with a hierarchy of types. For now we only support flat trees of types.
        """

        ml = self.metalang

        # We need to rewrite all parameters to give exclusive different names.
        vars_a = generate_action_arguments(ml, a, char='a_')
        vars_b = generate_action_arguments(ml, b, char='b_')
        substitution_a = {symref(param): arg for param, arg in zip(a.parameters, vars_a)}
        substitution_b = {symref(param): arg for param, arg in zip(b.parameters, vars_b)}

        # let's group action parameters by sort:
        vars_by_sort = defaultdict(list)
        for var in vars_a + vars_b:
            vars_by_sort[var.sort].append(symref(var))

        # Now we generate all possible combinations of equalities and disequalities
        grouped_vars, all_int_assignments = all_combinations_of_equalities(vars_by_sort)

        combinations_formulas = []
        combinations_substitutions = []
        # here we generate the formulas and compute the substitutions
        for element in all_int_assignments:
            mapping = generate_mapping_from_assignments(grouped_vars, element)
            # generate the equalities/disequalities from the int assignments
            case = generate_equalities(grouped_vars, element)
            # and combine them with the fixed ones
            combinations_formulas.append(land(*case, flat=True))
            combinations_substitutions.append(mapping)

        # Now lets check for each combination
        for idx_combination, substitution in enumerate(combinations_substitutions):
            # lets search which vars we have to check (only makes sense on vars that both actions modify)
            vars_to_check = []
            for a_eff in a.effects:
                for b_eff in b.effects:
                    modified_a = _get_affected_atom(a_eff)
                    modified_b = _get_affected_atom(b_eff)
                    what_a = substitute_expression(substitute_expression(modified_a, substitution_a), substitution)
                    what_b = substitute_expression(substitute_expression(modified_b, substitution_b), substitution)
                    if what_a.is_syntactically_equal(what_b):
                        vars_to_check.append((a_eff, b_eff))
            # check if we have something to check ...
            if len(vars_to_check) == 0:
                # print(f"[2] {a} with {b} \
                # when {combinations_formulas[idx_combination]} have nothing in common, so no point in continuing")
                continue

            # Now lets do the corresponding checks
            for a_eff, b_eff in vars_to_check:
                if combinations_formulas[idx_combination] in self.interferences[(a.name, b.name)] and \
                    not self.make_useless_checks:
                    continue  # This combination is already registered

                #print(f"[SC] we should check {a.name}{a_eff} with {b.name}{b_eff}")
                ## first we substitute action parameters and then our stuff
                exp1 = substitute_expression(substitute_expression(a_eff, substitution_a), substitution)
                exp2 = substitute_expression(substitute_expression(b_eff, substitution_b), substitution)

                ## Now we consider the effects as substitutions
                sigma_a = effect_as_substitution(exp1)
                sigma_b = effect_as_substitution(exp2)

                # and make the substitutions: Eff_a \sigma_b, and Eff_b \sigma_a
                exp1_s2 = apply_substitution_to_effect(exp1, sigma_b)
                exp2_s1 = apply_substitution_to_effect(exp2, sigma_a)

                neq_eff = neg(equiv(self.get_translated_effect(exp1_s2), self.get_translated_effect(exp2_s1)))
                vart = _get_timestep_var(ml)
                final_formula = exists(vart, neq_eff)

                # TODO - hash the formula and check before sending to SMT solver, as it might already
                # TODO - have been checked, because some combination of parameters might not be
                # TODO - relevant for  this check
                model = self.solve_theory([final_formula], ml)
                if model:
                    # print(f"[SC] SAT: they are NOT simply commuting when: {combinations_formulas[idx_combination]}")
                    self.update_interferences(a, b, combinations_formulas[idx_combination], commutative=True, label="S")
                    continue # No sense in checking other effects for SC, as it is already non SC on one.
                else:
                    pass
                    # print(f"[SC] UNSAT, this means that they are \
                    # simply commuting when {combinations_formulas[idx_combination]}")


    def check1(self, a, b):
        """
        Given action schemas a and b:
        Checks if a can restrict b's execution. i.e.:
        Pre_a /\ Pre_b /\ not(Pre_b sigma_a) is T-satisfiable
        """
        ml = self.metalang

        # We need to rewrite all parameters to give exclusive different names.
        vars_a = generate_action_arguments(ml, a, char='a_')
        vars_b = generate_action_arguments(ml, b, char='b_')
        substitution_a = {symref(param): arg for param, arg in zip(a.parameters, vars_a)}
        substitution_b = {symref(param): arg for param, arg in zip(b.parameters, vars_b)}

        # let's group action parameters by sort:
        vars_by_sort = defaultdict(list)
        for var in vars_a + vars_b:
            vars_by_sort[var.sort].append(symref(var))

        # Now we generate all possible combinations of equalities and disequalities
        grouped_vars, all_int_assignments = all_combinations_of_equalities(vars_by_sort)

        combinations_formulas = []
        combinations_substitutions = []
        # here we generate the formulas and compute the substitutions
        for element in all_int_assignments:
            mapping = generate_mapping_from_assignments(grouped_vars, element)
            # generate the equalities/disequalities from the int assignments
            case = generate_equalities(grouped_vars, element)
            # and combine them with the fixed ones
            combinations_formulas.append(land(*case, flat=True))
            combinations_substitutions.append(mapping)

        # Now we will check if Pre_a /\ Pre_b /\ not(Pre_b sigma_a) is T-satisfiable
        for idx_combination, substitution in enumerate(combinations_substitutions):
            if combinations_formulas[idx_combination] in self.interferences[(a.name, b.name)] and \
                not self.make_useless_checks:
                continue # This combination is already registered

            # first we substitute action parameters
            pre_a = substitute_expression(a.precondition, substitution_a)
            pre_b = substitute_expression(b.precondition, substitution_b)

            # and then our stuff
            spre_a = substitute_expression(pre_a, substitution)
            spre_b = substitute_expression(pre_b, substitution)

            # sigma_a will be the whole effect of substitutions. Here we operate on the premise
            # than an action CANNOT modify the same thing twice.
            sigma_a = {}
            for eff in a.effects:
                sub = effect_as_substitution(eff)
                key = list(sub.keys())[0]  # we only have one pair of key-value
                val = list(sub.values())[0]
                key = substitute_expression(substitute_expression(key.expr, substitution_a), substitution)
                val = substitute_expression(substitute_expression(val, substitution_a), substitution)
                sigma_a[symref(key)] = val
            pre_b_sigma_a = substitute_expression(spre_b, sigma_a)

            # construct the formula
            vart = _get_timestep_var(ml)
            final_formula = exists(vart, land(spre_b, spre_a, neg(pre_b_sigma_a), flat=True))
            final_formula = self.to_metalang(final_formula, vart, subt=vart)

            # TODO - hash the formula and check before sending to SMT solver, as it might already
            # TODO - have been checked, because some combination of parameters might not be
            # TODO - relevant for  this check
            model = self.solve_theory([final_formula], ml)
            if model:
                # print(f"[1] SAT: {a} interferes with {b}: {combinations_formulas[idx_combination]}")
                self.update_interferences(a, b, combinations_formulas[idx_combination], commutative=False, label="1")
            else:
                pass
                # print(f"[1] UNSAT, this means that {a} does not interfere with {b} when {combinations_formulas[idx_combination]}")

    def check2(self, a, b):
        """
        Given action schemas a and b:
        Checks if the combination of effects is invalid. i.e.:
        either:
            - a and b are not simply commuting, or
            - Pre_a /\ Pre_b /\ not ( x sigma_h({a,b}) = x sigma_b sigma_a) is T-satisfiable
        """
        # TODO: This is only defined for simply commuting actions, therefore we should filter this application
        ml = self.metalang

        # We need to rewrite all parameters to give exclusive different names.
        vars_a = generate_action_arguments(ml, a, char='a_')
        vars_b = generate_action_arguments(ml, b, char='b_')
        substitution_a = {symref(param): arg for param, arg in zip(a.parameters, vars_a)}
        substitution_b = {symref(param): arg for param, arg in zip(b.parameters, vars_b)}

        # let's group action parameters by sort:
        vars_by_sort = defaultdict(list)
        for var in vars_a + vars_b:
            vars_by_sort[var.sort].append(symref(var))

        # Now we generate all possible combinations of equalities and disequalities
        grouped_vars, all_int_assignments = all_combinations_of_equalities(vars_by_sort)

        combinations_formulas = []
        combinations_substitutions = []
        # here we generate the formulas and compute the substitutions
        for element in all_int_assignments:
            mapping = generate_mapping_from_assignments(grouped_vars, element)
            # generate the equalities/disequalities from the int assignments
            case = generate_equalities(grouped_vars, element)
            # and combine them with the fixed ones
            combinations_formulas.append(land(*case, flat=True))
            combinations_substitutions.append(mapping)

        # Now we will check if Pre_a /\ Pre_b /\ not (x sigma_h({a, b}) = x sigma_b sigma_a) is T - satisfiable
        # i.e., if a affects b. Lets have an example:
        # Lets suppose we have a = <T, x=x+1, y=y+1> b = <T, y=y+x>
        #
        # to calculate h({a,b}), sequentially, for each variable, we apply substitutions derived from
        # effects, first by a and then by b. Note that due to simply commutativity, its the same in the
        # reversed order.
        # x = x || x = x + 1 || x = x + 1
        # y = y || y = y + 1 || y = (y+x) + 1
        # h({a,b}) = <T, x=x+1, y=(y+x)+1>
        #
        # Now, to calculate sigma_b sigma_a over a variable, we first apply all effects of b and then all of a
        # x = x || x = x || x = x + 1
        # y = y || y = y + x || y = (y+1) + (x+1)
        # sigma_b sigma_a = < x = x + 1, y = (y+1) + (x+1)>
        #
        # OTOH, to calculate sigma_a sigma_b, we first apply all effects of a and then all of b
        # x = x || x = x || x = x + 1
        # y = y || y = y + 1 || y = (y+x) + 1
        # sigma_a sigma_b = < x = x+1, y= (y+x) + 1>
        #
        # In this example, a affects b, as h({a,b}) != sigma_b sigma_a,
        # but not the other way around, as h({a,b}) = sigma_a sigma_b
        for idx_combination, substitution in enumerate(combinations_substitutions):
            if combinations_formulas[idx_combination] in self.interferences[(a.name, b.name)] and \
                not self.make_useless_checks:
                continue # This combination is already registered

            # first we substitute action parameters
            pre_a = substitute_expression(a.precondition, substitution_a)
            pre_b = substitute_expression(b.precondition, substitution_b)
            # and then our stuff
            spre_a = substitute_expression(pre_a, substitution)
            spre_b = substitute_expression(pre_b, substitution)

            # sigma_x will be the whole effect of substitutions. Here we operate on the premise
            # than an action CANNOT modify the same thing twice.
            sigma_a = effects_as_fixed_substitution(a, substitution_a, substitution)
            sigma_b = effects_as_fixed_substitution(b, substitution_b, substitution)

            # lets search which vars we have to check (only makes sense on vars that both actions modify)
            vars_to_check = []
            for a_eff in a.effects:
                for b_eff in b.effects:
                    modified_a = _get_affected_atom(a_eff)
                    modified_b = _get_affected_atom(b_eff)
                    what_a = substitute_expression(substitute_expression(modified_a, substitution_a), substitution)
                    what_b = substitute_expression(substitute_expression(modified_b, substitution_b), substitution)
                    if what_a.is_syntactically_equal(what_b):
                        # print(f"[2] we have to consider {what_a} == {what_b}, as {a.name} and {b.name} both talk about it")
                        vars_to_check.append(what_a)
            # check if we have something to check ...
            if len(vars_to_check) == 0:
                # print(f"[2] {a} with {b} when {combinations_formulas[idx_combination]} have nothing in common, so no point in continuing")
                continue

            # construct the formula: not (x sigma_h({a, b}) = x sigma_b sigma_a)
            serial_execution = []
            for var in vars_to_check:
                h_ab = calc_happening_a_b(var, sigma_a, sigma_b)
                sig_ba = calc_sigma_b_a(var, sigma_a, sigma_b)
                # print(f"[2] for {var} and\n\t sigma_a = {sigma_a},\n\t sigma_b = {sigma_b}")
                # print(f"[2] happening(a,b) = {h_ab}, sigma(b,a) = {sig_ba}")
                if isinstance(h_ab, CompoundFormula):
                    serial_execution.append(neg(equiv(h_ab, sig_ba)))
                elif isinstance(h_ab, CompoundTerm):
                    serial_execution.append(neg(h_ab == sig_ba))

            vart = _get_timestep_var(ml)
            final_formula = exists(vart, land(spre_b, spre_a, lor(*serial_execution, flat=True), flat=True))
            final_formula = self.to_metalang(final_formula, vart, subt=vart)

            # TODO - hash the formula and check before sending to SMT solver, as it might already
            # TODO - have been checked, because some combination of parameters might not be
            # TODO - relevant for  this check
            model = self.solve_theory([final_formula], ml)
            if model:
                # print(f"[2] SAT: {a} interferes with {b}: {combinations_formulas[idx_combination]}")
                self.update_interferences(a, b, combinations_formulas[idx_combination], commutative=False, label="2")
            else:
                pass
                # print(f"[2] UNSAT, this means that {a} does not interfere with {b} \
                # when {combinations_formulas[idx_combination]}")

    def update_interferences(self, a1, a2, combination, commutative=False, label='no-label'):

        print(f"[{label}] {a1.name} -> {a2.name} when {combination}")
        self.interferences[(a1.name, a2.name)].add(combination)
        if commutative:
            print(f"[{label}] {a2.name} -> {a1.name} when {combination}")
            self.interferences[(a2.name, a1.name)].add(combination)

    def get_translated_effect(self, eff):
        """ translate the effects to the metalang """
        ml = self.metalang
        vart = _get_timestep_var(ml)

        # Prepend the effect condition, if necessary, and translate:
        if not isinstance(eff.condition, Tautology):
            antec = self.to_metalang(eff.condition, vart)
        else:
            antec = top

        if isinstance(eff, fs.AddEffect):
            trans_eff = implies(antec, self.to_metalang(eff.atom, vart + 1, subt=vart))

        elif isinstance(eff, fs.DelEffect):
            trans_eff = implies(antec, self.to_metalang(~eff.atom, vart + 1, subt=vart))

        elif isinstance(eff, fs.FunctionalEffect):
            lhs = self.to_metalang(eff.lhs, vart + 1, subt=vart)
            rhs = self.to_metalang(eff.rhs, vart, subt=vart)
            trans_eff = implies(antec, lhs == rhs)
        else:
            raise TransformationError(f"Can't compile effect {eff}")
        return trans_eff

    def symbol_is_fluent(self, symbol):
        """ returns True if a given symbol is a fluent, i.e. it can change over time steps """
        return not symbol.builtin and symbol not in self.static_symbols

    def solve_theory(self, theory, language):
        """ given a theory, solve it. TODO: translator """
        # Some sanity check: All formulas must be sentences!
        for formula in theory:
            freevars = free_variables(formula)
            if freevars:
                raise TransformationError(f'Formula {formula} has unexpected free variables: {freevars}')

        # Once we have the theory in Tarski format, let's just translate it into PySMT format:
        # with resources.timing(f"Translating and solving", newline=True):
        anames = set(a.name for a in self.problem.actions.values())
        translator = PySMTTranslator(language, self.static_symbols, anames)
        # print(f"theory: {theory}")
        translated = translator.translate(theory)
        # print(f"translated: {translated}")

        # Let's simplify the sentences for further clarity
        # translator.print_as_smtlib(translated, {}, sys.stdout)
        translated = translator.simplify(translated)
        # translator.print_as_smtlib(translated, {}, sys.stdout)

        model = solve(translated, 'z3', silent=True)
        return model  # decode_smt_model(model, horizon, translator)

    def get_expression_bounds(self, expr):
        s = expr.sort
        # Note that bounds in Tarski intervals are inclusive, while here we expect an exclusive upper bound
        return (s.lower_bound, s.upper_bound + 1) if isinstance(s, Interval) else self.sort_bounds[s]


def effects_as_fixed_substitution(a, substitution_a, vars_substitution):
    """ Given an action a, return the effects of the action as a whole substitution"""
    sigma_a = {}
    for eff in a.effects:
        sub = effect_as_substitution(eff)
        key, val = list(sub.items())[0]  # we only have one pair of key-value
        key = substitute_expression(substitute_expression(key.expr, substitution_a), vars_substitution)
        val = substitute_expression(substitute_expression(val, substitution_a), vars_substitution)
        sigma_a[symref(key)] = val
    return sigma_a


def effect_as_substitution(eff):
    """
     This function will, given an action and one of its effects, return the effect as a metalang substitution
    """
    # a clean dict to store the effect as a substitution
    substitution = {}
    # An add effect means identity substitution
    if isinstance(eff, fs.AddEffect):
        # first we translate to the metalang, then make the substitutions
        x_t = eff.atom
        substitution[symref(x_t)] = x_t
    elif isinstance(eff, fs.DelEffect):
        x_t = eff.atom
        substitution[symref(x_t)] = neg(eff.atom)
    elif isinstance(eff, fs.FunctionalEffect):
        x_t = eff.lhs
        substitution[symref(x_t)] = eff.rhs
    else:
        print(f"What is {eff}? Baby don't hurt me!")
    return substitution


def apply_substitution_to_effect(eff, substitution):
    if isinstance(eff, fs.AddEffect):
        # first we translate to the metalang, then make the substitutions
        return fs.AddEffect(substitute_expression(eff.atom, substitution))
    elif isinstance(eff, fs.DelEffect):
        return fs.DelEffect(substitute_expression(eff.atom, substitution))
    elif isinstance(eff, fs.FunctionalEffect):
        return fs.FunctionalEffect(eff.lhs, substitute_expression(eff.rhs, substitution))
    else:
        print(f"What is {eff}? Baby don't hurt me!")


# auxiliary functions stolen from the lifted encoding file
def generate_action_arguments(lang, act, char='z'):
    binding = [lang.variable(f"{char}{i}", lang.get_sort(v.sort.name)) for i, v in enumerate(act.parameters, start=1)]
    return binding


def _get_timestep_sort(lang):
    return lang.Timestep


def _get_timestep_var(lang, name="t"):
    return lang.variable(name, _get_timestep_sort(lang))


def _get_timestep_term(lang, value):
    if isinstance(value, Term):
        return value
    return _get_timestep_sort(lang).cast(value)


def _get_affected_atom(eff):
    """ Given an effect, it returns the predicate that is changed """
    return eff.atom if isinstance(eff, (fs.AddEffect, fs.DelEffect)) else eff.lhs


def generate_set_partitions(n, shift=0):
    """
    Based on Michael Orlov: Efficient Generation of Set Partitions.
    "https://www.cs.bgu.ac.il/~orlovm/papers/"
    n: size
    shift: how many naturals the generation must be shifted
    """
    assert (n > 0)
    kappa = [0] * n
    M = [0] * n

    def generator():
        for i in range(n - 1, 0, -1):
            if kappa[i] <= M[i - 1]:
                kappa[i] += 1
                new_max = max(M[i], kappa[i])
                M[i] = new_max
                for j in range(i + 1, n):
                    kappa[j] = 0
                    M[j] = new_max
                return True
        return False

    total = []
    # initial step
    tmp_v = copy.copy(kappa)
    for idx in range(0, len(tmp_v)):
        tmp_v[idx] += shift
    total.append(tmp_v)

    # rest of steps
    while generator():
        tmp_v = copy.copy(kappa)
        for idx in range(0, len(tmp_v)):
            tmp_v[idx] += shift
        total.append(tmp_v)

    return total


def all_combinations_of_equalities(vars_by_sort):
    """
        Given a dict of sorts to variables, generate all possible
        combinations of equalities and disequalities between them
        Returns two things:
            - the list of lists of variables by type: [ [a, b] , [c] ]
            - a list such as: [ [ 0, 1], [0] ], ...
              where the equalities are for further use.
    """
    # a list of lists of variables, grouped by sort
    grouped_list_sorts = list(vars_by_sort.keys())
    elements_by_sort = [list(i.domain()) for i in grouped_list_sorts]
    # print(type(list(grouped_list_sorts[0].domain())[0]))
    grouped_list_vars = list(vars_by_sort.values())

    set_partitions = []
    for idx_list, list_vars in enumerate(grouped_list_vars):
        combinations = generate_set_partitions(len(list_vars))

        # if we have a set of variables of a given sort, and there is more combinations than
        # objects in that sort, we will filter the combinations that have more different elements
        # than objects in that sort. i.e., a sort "aircraft" with only one object and two variables
        # will generate [0,0],[0,1]. We will filter the [0,1] (as it cannot be different from itself)
        len_group = len(elements_by_sort[idx_list])
        combinations = [x for x in combinations if len(set(x)) <= len_group]
        # print(f"len_group: {len_group} {combinations}")
        set_partitions.append(combinations)

    # OK now we substitute by elements of the current domain ....
    for idx_sort, combinations in enumerate(set_partitions):
        for idx_combination, combination in enumerate(combinations):
            combinations[idx_combination] = [elements_by_sort[idx_sort][x] for x in combination]

    # each possible combination of the different assignments and types
    all_int_assignments = list(itertools.product(*set_partitions))
    return grouped_list_vars, all_int_assignments


def generate_equalities(list_vars, list_numbers):
    equalities = []
    for idx_type, group in enumerate(list_numbers):
        # Here we are going an extra mile to avoid adding some extra constraints that are obvious
        # per the equality transitivity closure, using the `equality_done` variable.
        #
        # For example, for variables [a,b,c] and a group [0,0,0], we only need two
        # equalities a = b and b = c, as per transitivity the solver will deduce that a = c.
        for idx_var1, var1 in enumerate(list_vars[idx_type]):
            equality_done = False
            idx_var2 = idx_var1 + 1  # we dont want to compare a var with itself
            while idx_var2 < len(list_vars[idx_type]):
                var2 = list_vars[idx_type][idx_var2]
                # Note that equality is transitive, while disequality isn't, so we need all pairs
                if group[idx_var1].symbol != group[idx_var2].symbol:
                    equalities.append(var1.expr != var2.expr)
                # if we find another further in the list that has same value and still not added equality, do it
                elif not equality_done:
                    equalities.append(var1.expr == var2.expr)
                    equality_done = True
                idx_var2 += 1
    return equalities


def generate_mapping_from_assignments(grouped_vars, assignments):
    """
    Given a list of lists variables and a list of lists integers,
    such as [ [ var_a, var_b ] , [ var_c ], .... and [ [ 1, 2] , [ 3 ....
     match them by index, generating a substitution { var_a : 1, var_b : 2 ....}
    """
    flat_vars = list(itertools.chain(*grouped_vars))  # we flatten the list of lists
    flat_ints = list(itertools.chain(*assignments))
    return {var: val for var, val in zip(flat_vars, flat_ints)}


def filter_assignments(grouped_vars, all_int_assignments, equalities):
    """
    Given a list of assignments, filter the ones that do not match with the given equalities
    :param grouped_vars:  list of vars appearing, grouped by type, such as  [ [ var_a, var_b ] , [ var_c ],
    :param all_int_assignments: list of assignments, each in the form, also grouped by type [ [ 1, 2] , [ 3 ....
    :param equalities: list of equalities
    :return: the all_int_assignments, filtered.
    """
    # if the combination does not match what we already know, filter it
    filtered_assignments = []
    flattened_vars = list(itertools.chain(*grouped_vars))
    for mapping in all_int_assignments:
        adhere_to_equalities = False
        flattened_mapping = list(itertools.chain(*mapping))  # flat the integer list

        value_map = {}  # we index the  values
        for idx, _ in enumerate(flattened_vars):
            value_map[flattened_vars[idx]] = symref(flattened_mapping[idx])

        # now lets filter
        for established_eq in equalities:
            var1 = symref(established_eq.subterms[0])
            var2 = symref(established_eq.subterms[1])
            if value_map[var1] != value_map[var2]:
                # print(f"mapping {mapping} do not adhere to established equality {established_eq}")
                adhere_to_equalities = True
                break

        # if it does not break any rule, add to the list
        if not adhere_to_equalities:
            filtered_assignments.append(mapping)
    return filtered_assignments


def calc_happening_a_b(var, sigma_a, sigma_b):
    """ Given a variable and two effects, calculate the happening of {a,b} """
    var_happening_a_b = copy.deepcopy(var)
    for key, value in sigma_a.items():
        if key.expr.is_syntactically_equal(var):
            var_happening_a_b = substitute_expression(var_happening_a_b, {key: value})

    for key, value in sigma_b.items():
        if key.expr.is_syntactically_equal(var):
            var_happening_a_b = substitute_expression(var_happening_a_b, {key: value})
    return var_happening_a_b


def calc_sigma_b_a(var, sigma_a, sigma_b):
    """ Given a variable and two effects, calculate the variable after applying first b and then a """
    return substitute_expression(substitute_expression(var, sigma_b), sigma_a)

#   def simply_commuting_old(self, a, b):
#       """
#       Given action schemas a and b:
#       Check in what cases the action schemas are not simply commuting. i.e:
#       if not(sigma_a = sigma_b) is T-satisfiable

#       TODO: Take into account variables in the quantifiers
#       TODO: Look more closely what happens with a hierarchy of types. For now we only support flat trees of types.
#       """
#       ml = self.metalang
#       # Do we really need this?
#       self.metalang.Timestep.set_bounds(0, 2)

#       for a_eff in a.effects:
#           for b_eff in b.effects:
#               modified_a = _get_affected_atom(a_eff)
#               modified_b = _get_affected_atom(b_eff)
#               # Must check for each pair of effects in case they talk about the same predicate
#               if modified_a.symbol == modified_b.symbol:

#                   # We need to rewrite all parameters to give exclusive different names.
#                   vars_a = generate_action_arguments(ml, a, char='a_')
#                   vars_b = generate_action_arguments(ml, b, char='b_')
#                   substitution_a = {symref(param): arg for param, arg in zip(a.parameters, vars_a)}
#                   substitution_b = {symref(param): arg for param, arg in zip(b.parameters, vars_b)}

#                   # let's group action parameters by sort:
#                   vars_by_sort = defaultdict(list)
#                   for var in vars_a + vars_b:
#                       vars_by_sort[var.sort].append(symref(var))

#                   # According to the definition 3.5 in the paper, we are checking only assignments to the same
#                   # variable here. This means in the lifted setting that all parameters of the fluent at hand
#                   # must be equal. Therefore, we can capture the variables appearing in the lhs of the two
#                   # effects and:
#                   # - remove them from further processing business, as we're assuming they're equal.
#                   equalities = []  # fixed equalities between parameters
#                   for idx, _ in enumerate(modified_a.subterms):
#                       var1 = substitution_a[symref(modified_a.subterms[idx])]
#                       var2 = substitution_b[symref(modified_b.subterms[idx])]
#                       equalities.append(var1 == var2)

#                   # Now we generate all possible combinations of equalities and disequalities
#                   grouped_vars, all_int_assignments = all_combinations_of_equalities(vars_by_sort)
#                   # if the combination does not match what we already know, filter it
#                   filtered_int_assignments = filter_assignments(grouped_vars, all_int_assignments, equalities)

#                   combinations_formulas = []
#                   combinations_substitutions = []
#                   # here we generate the formulas and compute the substitutions
#                   for element in filtered_int_assignments:
#                       mapping = generate_mapping_from_assignments(grouped_vars, element)
#                       # generate the equalities/disequalities from the int assignments
#                       case = generate_equalities(grouped_vars, element)
#                       # and combine them with the fixed ones
#                       combinations_formulas.append(land(*(case), flat=True))
#                       combinations_substitutions.append(mapping)

#                   # Then in the problem we should phrase the question i.e.  Eff_a \sigma_b, and Eff_b \sigma_a
#                   # and do an allsolutions considering all the possible combinations of equality and inequalities
#                   # between action parameters.
#                   for idx_combination, substitution in enumerate(combinations_substitutions):
#                       # first we substitute action parameters
#                       sa_eff = substitute_expression(a_eff, substitution_a)
#                       sb_eff = substitute_expression(b_eff, substitution_b)
#                       # and then our stuff
#                       exp1 = substitute_expression(sa_eff, substitution)
#                       exp2 = substitute_expression(sb_eff, substitution)
#                       # Now we consider the effects as substitutions
#                       sigma_a = effect_as_substitution(exp1)
#                       sigma_b = effect_as_substitution(exp2)

#                       # and make the substitutions: Eff_a \sigma_b, and Eff_b \sigma_a
#                       exp1_s2 = apply_substitution_to_effect(exp1, sigma_b)
#                       exp2_s1 = apply_substitution_to_effect(exp2, sigma_a)

#                       # ------- Some debug statements -------
#                       # print(f"\nsubstitution of sigmas onto effects\n-----------")
#                       # print(f"Applying {sigma_b}\n\t to {exp1}\n\t leads to: {exp1_s2}")
#                       # print(f"Applying {sigma_a}\n\t to {exp2}\n\t leads to: {exp2_s1}")
#                       # # finally lets check if not (sigma_a = sigma_b) is T - satisfiable

#                       # construct not (sigma_a = sigma_b)
#                       neq_eff = neg(equiv(self.get_translated_effect(exp1_s2), self.get_translated_effect(exp2_s1)))
#                       vart = _get_timestep_var(ml)
#                       final_formula = exists(vart, neq_eff)

#                       # TODO - hash the formula and check before sending to SMT solver, as it might already
#                       # TODO - have been checked, because some combination of parameters might not be
#                       # TODO - relevant for  this check
#                       model = self.solve_theory([final_formula], ml)
#                       if model:
#                           # print(f"[SC] SAT: they are NOT simply commuting when: {combinations_formulas[idx_combination]}")
#                           self.interferences[(a,b)].append(combinations_formulas[idx_combination])
#                           self.interferences[(b,a)].append(combinations_formulas[idx_combination])
#                       else:
#                           pass
#                           # print(f"[SC] UNSAT, this means that they are simply commuting when {combinations_formulas[idx_combination]}")