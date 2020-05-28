import itertools
from collections import OrderedDict, defaultdict

import tarski
import tarski.fstrips as fs
from tarski import Term
from tarski.fstrips import FunctionalEffect
from tarski.fstrips.manipulation.simplify import simplify_existential_quantification, Simplify
from tarski.fstrips.representation import classify_atom_occurrences_in_formula
from tarski.syntax import symref, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Contradiction, term_substitution, forall, land, implies, lor, exists, Constant, Variable, Predicate, sorts
from tarski.syntax.formulas import quantified
from tarski.syntax.ops import flatten
from tarski.syntax.sorts import parent, compute_signature_bindings, Interval
from tarski.syntax.util import get_symbols
from tarski.theories import Theory

from ..errors import TransformationError
from ..interferences import SemanticInterferences


class FullyLiftedEncoding:
    """ A fully lifted encoding for a fixed horizon, using quantifiers over both timesteps and
    action parameters. """

    def __init__(self, problem: fs.Problem, static_symbols, operators=None, statevars=None):
        self.problem = problem
        self.static_symbols = static_symbols
        self.operators = operators
        self.statevars = statevars
        self.lang = problem.language

        self.choice_symbols = compute_choice_symbols(problem.language, problem.init)
        self.sort_map = dict()  # A map from sorts in the original language to sorts in the metalanguage
        self.metalang = self.setup_metalang(problem)

        # A map from compound terms to corresponding state variables
        # self.statevaridx = _index_state_variables(statevars)
        # self.interferences, self.mutexes = self.compute_interferences(self.operators)
        self.interferences = SemanticInterferences(self.problem, self.static_symbols).get_interferences()

        self.eff_index = analyze_action_effects(self.metalang, problem.actions.values())
        self.gamma_pos, self.gamma_neg, self.gamma_fun = self.compute_gammas(problem, self.metalang)

        self.vars = OrderedDict()

        self.custom_domain_terms = OrderedDict()
        self.theory = []

        # We'll create some comments indexed by the index of the self.theory element to which they refer.
        # They will be used to increase the clarity while debugging, in SMTLIB outputs, etc.
        self.comments = {}

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

    def compute_gammas(self, problem, ml):
        """ Compute the gamma sentences for all (fluent) symbols """
        lang = problem.language
        gamma_pos = dict()
        gamma_neg = dict()
        gamma_f = dict()

        for s in get_symbols(lang, type_="all", include_builtin=False):
            if not self.symbol_is_fluent(s):
                continue

            if isinstance(s, Predicate):
                gamma_pos[s.name] = self.compute_gamma(ml, s, self.eff_index['add'])
                gamma_neg[s.name] = self.compute_gamma(ml, s, self.eff_index['del'])
            else:
                gamma_f[s.name] = self.compute_gamma(ml, s, self.eff_index['fun'])

        return gamma_pos, gamma_neg, gamma_f

    def compute_gamma(self, ml, symbol, idx):
        tvar = _get_timestep_var(ml)

        disjuncts = []
        for act, eff in idx[symbol.name]:
            action_binding = generate_action_arguments(ml, act)
            action_happens_at_t = ml.get_predicate(act.name)(*action_binding, tvar)
            effcond = self.to_metalang(eff.condition, tvar)
            gamma_binding = self.compute_gamma_binding(ml, eff, symbol)

            gamma_act = land(action_happens_at_t, effcond, *gamma_binding, flat=True)
            if action_binding:  # exist-quantify the action parameters other than the timestep t
                gamma_act = exists(*action_binding, gamma_act)

            # We chain a couple of simplifications of the original gamma expression
            gamma_act = Simplify().simplify_expression(simplify_existential_quantification(gamma_act))

            disjuncts.append(gamma_act)
        return lor(*disjuncts, flat=True)

    def compute_gamma_binding(self, ml, eff, symbol):
        sym_args = generate_symbol_arguments(ml, symbol)
        tvar = _get_timestep_var(ml)

        if isinstance(eff, FunctionalEffect):
            yvar = ml.variable("y", ml.get_sort(symbol.codomain.name))
            y_bound = [yvar == self.to_metalang(eff.rhs, tvar)]
            lhs_binding = [self.to_metalang(st, tvar) for st in eff.lhs.subterms]
            return y_bound + [x == y for x, y in zip(sym_args, lhs_binding)]
        else:
            effect_binding = [self.to_metalang(st, tvar) for st in eff.atom.subterms]
            return [x == y for x, y in zip(sym_args, effect_binding)]

    def generate_theory(self, horizon):
        """ The main entry point to the class, generates the entire logical theory
        for a given horizon. """
        # Force the given horizon into the timestep sort
        self.metalang.Timestep.set_bounds(0, horizon)

        self.comments[len(self.theory)] = ";; Initial State:"
        self.assert_initial_state()

        self.comments[len(self.theory)] = ";; Goal condition:"
        self.goal(horizon)

        self.assert_frame_axioms()

        self.comments[len(self.theory)] = ";; Interference axioms:"
        self.assert_interference_axioms()

        for a in self.problem.actions.values():
            self.comments[len(self.theory)] = f";; Precondition and effects of action {a}:"
            self.assert_action(a)

        return self.metalang, self.theory, self.comments

    def is_state_variable(self, expression):
        return symref(expression) in self.statevaridx

    def compute_interferences(self, operators):
        # TODO Deprecated - to be removed
        posprec = defaultdict(list)
        negprec = defaultdict(list)
        funprec = defaultdict(list)
        addeff = defaultdict(list)
        deleff = defaultdict(list)
        funeff = defaultdict(list)
        addalleff = defaultdict(list)
        delalleff = defaultdict(list)
        funalleff = defaultdict(list)

        mutexes = set()
        interferences = defaultdict(list)

        # Classify precondition atoms
        for op in operators:
            pos, neg, fun = classify_atom_occurrences_in_formula(op.precondition)
            _ = [posprec[a].append(str(op)) for a in pos]
            _ = [negprec[a].append(str(op)) for a in neg]
            _ = [funprec[a].append(str(op)) for a in fun]

        # Analyze effects
        for op in operators:
            for eff in op.effects:
                if not isinstance(eff, (fs.AddEffect, fs.DelEffect, fs.FunctionalEffect)):
                    raise TransformationError(f'Cannot handle effect "{eff}"')
                atom = eff.atom if isinstance(eff, (fs.AddEffect, fs.DelEffect)) else eff.lhs

                if self.is_state_variable(atom):
                    if isinstance(eff, fs.AddEffect):
                        addeff[symref(atom)].append(str(op))
                    elif isinstance(eff, fs.DelEffect):
                        deleff[symref(atom)].append(str(op))
                    else:
                        funeff[symref(atom)].append(str(op))
                else:
                    if isinstance(eff, fs.AddEffect):
                        addalleff[atom.predicate].append(str(op))
                    elif isinstance(eff, fs.DelEffect):
                        delalleff[atom.predicate].append(str(op))
                    else:
                        funalleff[atom.predicate].append(str(op))

        def add_mutex(op1, op2):
            if str(op1) != str(op2):
                mutexes.add(frozenset({str(op1), str(op2)}))

        # Compute mutexes
        for op in operators:
            for eff in op.effects:
                atom = eff.atom if isinstance(eff, (fs.AddEffect, fs.DelEffect)) else eff.lhs
                if self.is_state_variable(atom):

                    if isinstance(eff, fs.AddEffect):
                        for conflict in itertools.chain(negprec[symref(atom)], deleff[symref(atom)], delalleff[atom.predicate]):
                            add_mutex(op, conflict)

                    elif isinstance(eff, fs.DelEffect):
                        for conflict in itertools.chain(posprec[symref(atom)], addeff[symref(atom)], addalleff[atom.predicate]):
                            add_mutex(op, conflict)
                    else:
                        for conflict in itertools.chain(funprec[symref(atom)], funeff[symref(atom)], funalleff):
                            add_mutex(op, conflict)
                        # TODO We need to take into account the RHS !!

        return interferences, mutexes

    def assert_initial_state(self):
        for p in get_symbols(self.lang, type_="all", include_builtin=False):
            if self.symbol_is_choice(p):
                continue  # The value of choice symbols is not determined a priori
            for binding in compute_signature_bindings(p.domain):
                expr = p(*binding)

                if isinstance(p, Predicate):
                    x = expr if self.problem.init[expr] else ~expr
                    self.theory.append(self.to_metalang(x, 0))
                else:
                    self.theory.append(self.to_metalang(expr == self.problem.init[expr], 0))

    def goal(self, t):
        self.theory.append(self.to_metalang(self.problem.goal, t))

    def assert_action(self, op):
        """ For given operator op and timestep t, assert the SMT expression:
                op@t --> op.precondition@t
                op@t --> op.effects@(t+1)
        """
        ml = self.metalang
        vart = _get_timestep_var(ml)
        apred = ml.get_predicate(op.name)

        vars_ = generate_action_arguments(ml, op)  # Don't use the timestep arg
        substitution = {symref(param): arg for param, arg in zip(op.parameters, vars_)}
        args = vars_ + [vart]
        happens = apred(*args)

        prec = term_substitution(flatten(op.precondition), substitution)
        a_implies_prec = forall(*args, implies(happens, self.to_metalang(prec, vart)))
        self.theory.append(a_implies_prec)

        for eff in op.effects:
            eff = term_substitution(eff, substitution)
            antec = happens

            # Prepend the effect condition, if necessary:
            if not isinstance(eff.condition, Tautology):
                antec = land(antec, self.to_metalang(eff.condition, vart))

            if isinstance(eff, fs.AddEffect):
                a_implies_eff = implies(antec, self.to_metalang(eff.atom, vart+1, subt=vart))

            elif isinstance(eff, fs.DelEffect):
                a_implies_eff = implies(antec, self.to_metalang(~eff.atom, vart+1, subt=vart))

            elif isinstance(eff, fs.FunctionalEffect):
                lhs = self.to_metalang(eff.lhs, vart+1, subt=vart)
                rhs = self.to_metalang(eff.rhs, vart, subt=vart)
                a_implies_eff = implies(antec, lhs == rhs)
            else:
                raise TransformationError(f"Can't compile effect {eff}")
            self.theory.append(forall(*args, a_implies_eff))

    def assert_frame_axioms(self):
        ml = self.metalang
        tvar = _get_timestep_var(ml)

        # First deal with predicates;
        for p in get_symbols(self.lang, type_="all", include_builtin=False):
            if not self.symbol_is_fluent(p):
                continue

            self.comments[len(self.theory)] = f";; Frame axiom for symbol {p}:"
            lvars = generate_symbol_arguments(self.lang, p)
            atom = p(*lvars)
            fquant = generate_symbol_arguments(ml, p) + [tvar]

            if isinstance(p, Predicate):
                # pos: not p(x, t) and p(x, t+1)  => \gamma_p^+(x, t)
                # neg: p(x, t) and not p(x, t+1)  => \gamma_p^-(x, t)
                at_t = self.to_metalang(atom, tvar)
                at_t1 = self.to_metalang(atom, tvar + 1)

                pos = forall(*fquant, implies(~at_t & at_t1, self.gamma_pos[p.name]))
                neg = forall(*fquant, implies(at_t & ~at_t1, self.gamma_neg[p.name]))
                self.theory += [pos, neg]
            else:
                # fun: f(x, t) != f(x, t+1) => \gamma_f[y/f(x, t+1)]
                yvar = ml.variable("y", ml.get_sort(p.codomain.name))
                at_t = self.to_metalang(atom, tvar)
                at_t1 = self.to_metalang(atom, tvar+1)
                gamma_replaced = term_substitution(self.gamma_fun[p.name], {symref(yvar): at_t1})
                fun = forall(*fquant, implies(at_t != at_t1, gamma_replaced))
                self.theory += [fun]

    def assert_interference_axioms(self):
        ml = self.metalang
        tvar = _get_timestep_var(ml)
        for a1, a2 in itertools.combinations_with_replacement(self.problem.actions.values(), 2):
            a1_args = generate_action_arguments(ml, a1, char="x")
            a2_args = generate_action_arguments(ml, a2, char="y")

            a1_happens_at_t = ml.get_predicate(a1.name)(*a1_args, tvar)
            a2_happens_at_t = ml.get_predicate(a2.name)(*a2_args, tvar)

            allargs = a1_args + a2_args + [tvar]
            sentence = lor(~a1_happens_at_t, ~a2_happens_at_t)
            if a1.name == a2.name:
                x_neq_y = lor(*(x != y for x, y in zip(a1_args, a2_args)), flat=True)
                sentence = implies(x_neq_y, sentence)
            self.theory += [forall(*allargs, sentence)]

    def symbol_is_fluent(self, symbol):
        return not symbol.builtin and symbol not in self.static_symbols

    def symbol_is_choice(self, symbol):
        return symbol in self.choice_symbols

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

            # if phi.symbol in get_set_symbols():
            #     return op(lhs, rhs)

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


def bool_to_tarski_boolean(lang, value):
    assert isinstance(value, bool)
    return lang.get("True" if value else "False")


def _index_state_variables(statevars):
    indexed = dict()
    for v in statevars:
        indexed[symref(v.to_atom())] = v
    return indexed


def generate_symbol_arguments(lang, symbol, char='x'):
    return [lang.variable(f"{char}{i}", lang.get_sort(s.name)) for i, s in enumerate(symbol.domain, start=1)]


def generate_action_arguments(lang, act, char='z'):
    binding = [lang.variable(f"{char}{i}", lang.get_sort(v.sort.name)) for i, v in enumerate(act.parameters, start=1)]
    return binding
    # timestamp = [lang.variable("t", _get_timestep_sort(lang))]
    # return binding + timestamp


def analyze_action_effects(lang, schemas):
    """ Compile an index of action effects according to the type of effect (add/del/functional) and the
    symbol they affect. """
    index = {"add": defaultdict(list), "del": defaultdict(list), "fun": defaultdict(list)}

    for a in schemas:
        substitution = {symref(param): arg for param, arg in zip(a.parameters, generate_action_arguments(lang, a))}

        for eff in a.effects:
            if not isinstance(eff, (fs.AddEffect, fs.DelEffect, fs.FunctionalEffect)):
                raise TransformationError(f'Cannot handle effect "{eff}"')

            # Let's substitute the action parameters for some standard variable names such as z1, z2, ... so that
            # later on in the compilation we can use them off the self.
            eff = term_substitution(eff, substitution)
            atom = eff.atom if isinstance(eff, (fs.AddEffect, fs.DelEffect)) else eff.lhs

            if isinstance(eff, fs.AddEffect):
                index["add"][atom.symbol.name].append((a, eff))
            elif isinstance(eff, fs.DelEffect):
                index["del"][atom.symbol.name].append((a, eff))
            else:
                index["fun"][atom.symbol.name].append((a, eff))

    return index


def _get_timestep_sort(lang):
    return lang.Timestep


def _get_timestep_var(lang, name="t"):
    return lang.variable(name, _get_timestep_sort(lang))


def _get_timestep_term(lang, value):
    if isinstance(value, Term):
        return value
    return _get_timestep_sort(lang).cast(value)


def compute_choice_symbols(lang, init):
    # Note that ATM we cannot consider that predicate symbols without initial denotation are choice
    # symbols, because of the closed world assumption (i.e. no denotation already means emptyset denotation).
    # Of course we can devise some other mechanism to explicitly represent choice symbols that will avoid this problem.
    choices = set()
    for s in get_symbols(lang, type_="function", include_builtin=False):
        if s.signature not in init.function_extensions:
            choices.add(s)
    return choices
