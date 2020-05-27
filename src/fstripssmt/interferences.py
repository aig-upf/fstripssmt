import copy
import sys

from multipledispatch import dispatch
from pysmt.shortcuts import FreshSymbol, Symbol, EqualsOrIff, Int, Real, FunctionType, And, ForAll, Exists, get_env
from pysmt.shortcuts import LT, GE, Equals, Implies, Or, TRUE, FALSE, Not, Symbol
from pysmt.typing import INT, BOOL, REAL
from tarski.syntax.ops import all_variables
#from fstripssmt.runner import decode_smt_model
from tarski.syntax.ops import compute_sort_id_assignment
from fstripssmt.solvers.common import solve
from .solvers.pysmt import PySMTTranslator, print_as_smtlib
from .errors import TransformationError

import tarski
from tarski import Term
from tarski.syntax.ops import free_variables
from tarski.utils import resources
from tarski.syntax import top
from tarski.fstrips.walker import ProblemWalker
from tarski.grounding.ops import approximate_symbol_fluency
from tarski.syntax import symref, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
   Contradiction, term_substitution, forall, land, implies, lor, exists, Constant, Variable, Predicate
from tarski.syntax.formulas import quantified, neg, equiv
from tarski.syntax.sorts import parent, Interval
from tarski.syntax.util import get_symbols
import tarski.fstrips as fs


class SemanticInterferences(ProblemWalker):
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
        self.metalang = self.setup_metalang(problem)
        _, self.static_symbols = approximate_symbol_fluency(problem)
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.metalang)

    def setup_metalang(self, problem):
        """ Set up the Tarski metalanguage where we will build the SMT compilation. """
        lang = problem.language
        ml = tarski.fstrips.language(f"{lang.name}-smt", theories=["equality", "arithmetic"])

        # Declare all sorts
        for s in lang.sorts:
            if not s.builtin and s.name != "object":
                if isinstance(s, Interval):
                    ml.interval(s.name, parent(s).name, s.lower_bound, s.upper_bound)
                else:
                    ml.sort(s.name, parent(s).name)

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
        """ Transform a formula phi to a formula suitable for being translated to SMT directly
            parameters:
                - phi: formula
                - t : timestep variable
                - subt : shall we substitute the timestep for something?
        """
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
            if self.symbol_is_fluent(phi.symbol):
                args += (_get_timestep_const(ml, t),)

            return CompoundTerm(ml.get_function(phi.symbol.name), args)

        elif isinstance(phi, Atom):
            args = tuple(self.to_metalang(psi, subt) for psi in phi.subterms)
            if self.symbol_is_fluent(phi.symbol):
                args += (_get_timestep_const(ml, t),)

            return Atom(ml.get_predicate(phi.symbol.name), args)

        raise TransformationError(f"Don't know how to transform element or expression '{phi}' to the SMT metalanguage")

    def get_interferences(self):
        """ This method is our 'main', where we implement the logic """
        actions = self.problem.actions.values()
        for idx_a, a in enumerate(actions):
            for idx_b, b in enumerate(actions):
                # The check for simple commutativity is symmetric,
                # and therefore we do not need to check a,b and b,a.
                if idx_b >= idx_a:
                    self.simply_commuting(a, b)
        return []

    def simply_commuting(self, a, b):
        """
        Given action schemas a and b:
        Check if the action schemas are not simply commuting. i.e:
        if not(sigma_a = sigma_b) is T-satisfiable
        """
        ml = self.metalang

        # Must check for each pair of effects in case they talk about the same predicate
        for a_eff in a.effects:
            for b_eff in b.effects:
                modified_a = _get_affected_atom(a_eff)
                modified_b = _get_affected_atom(b_eff)
                if modified_a.symbol == modified_b.symbol:

                    print(f"as both talk about {modified_a.symbol}, lets check if they are simply commuting:")
                    print(f"\t action a:{a} --- effect:{a_eff} \n\t action b:{b} --- effect:{b_eff})")

                    # compute the substitutions
                    substitution = {}
                    self.effect_as_substitution(a_eff, substitution)
                    self.effect_as_substitution(b_eff, substitution)

                    # substitute the parameters on the effects
                    vars_a, subs_a, translated_a = self.get_translated_effect(a, a_eff, 'a_')
                    vars_b, subs_b, translated_b = self.get_translated_effect(b, b_eff, 'b_')

                    # and make the substitutions: Eff_a \sigma_b, and Eff_b \sigma_a
                    a_seff = term_substitution(translated_a, substitution)
                    b_seff = term_substitution(translated_b, substitution)

                    # ------- Some debug statements -------
                    print(substitution)
                    print(f"substituting {translated_a} into {translated_b} lends to: {a_seff}")
                    print(f"substituting {translated_b} into {translated_a} lends to: {b_seff}")

                    # construct not (sigma_a = sigma_b)
                    neq_eff = neg(equiv(translated_a,translated_b))

                    # we must force that parameters are the same to be able to say that we are talking
                    # about the same underlying variable (i.e. the same grounded var)
                    parameters_term_a = term_substitution(modified_a, subs_a).subterms
                    parameters_term_b = term_substitution(modified_b, subs_b).subterms
                    equalities = [ a == b for a, b in zip(parameters_term_a, parameters_term_b)]

                    # finally lets check if not (sigma_a = sigma_b) is T - satisfiable
                    # construct the problem and ask the SMT solver if SAT, break, else continue searching
                    vart = _get_timestep_var(ml)
                    all_vars = vars_a + vars_b + [vart]
                    final_formula = exists(*all_vars, land(*(equalities + [neq_eff])))
                    model = self.solve_theory([ final_formula ], ml)
                    if model:
                        print("SAT, this means that they are NOT simply commuting")
                        return True
                    else:
                        print("UNSAT, this means that they are simply commuting")
        return True


    def get_translated_effect(self, a, eff, prefix):
        """ translate the effects to the metalang """
        ml = self.metalang

        vart = _get_timestep_var(ml)
        vars_ = generate_action_arguments(ml, a, char=prefix)  # Don't use the timestep arg
        substitution_ = {symref(param): arg for param, arg in zip(a.parameters, vars_)}
        seff = term_substitution(eff, substitution_)

        # Prepend the effect condition, if necessary, and translate:
        if not isinstance(seff.condition, Tautology):
            antec = self.to_metalang(seff.condition, vart)
        else:
            antec = top

        if isinstance(seff, fs.AddEffect):
            trans_eff = implies(antec, self.to_metalang(seff.atom, vart + 1, subt=vart))

        elif isinstance(seff, fs.DelEffect):
            trans_eff = implies(antec, self.to_metalang(~seff.atom, vart + 1, subt=vart))

        elif isinstance(seff, fs.FunctionalEffect):
            lhs = self.to_metalang(seff.lhs, vart + 1, subt=vart)
            rhs = self.to_metalang(seff.rhs, vart, subt=vart)
            trans_eff = implies(antec, lhs == rhs)
        else:
            raise TransformationError(f"Can't compile effect {eff}")
        # finally return the encoded effect
        return vars_, substitution_, trans_eff

    def check1(self, a, b):
        """
        Given action schemas a and b:
        Checks if a can restrict b's execution. i.e.:
        Pre_a /\ Pre_b /\ not(Pre_b sigma_a) is T-satisfiable
        """
        pass

    def check2(self, a, b):
        """
        Given action schemas a and b:
        Checks if the combination of effects is invalid. i.e.:
        either:
            - a and b are not simply commuting, or
            - Pre_a /\ Pre_b /\ not ( x sigma_h({a,b}) = x sigma_b sigma_a) is T-satisfiable
        """
        pass

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
        horizon = 2 # we only check t and t+1, i.e. one transition
        with resources.timing(f"Translating and solving", newline=True):
            anames = set(a.name for a in self.problem.actions.values())
            translator = PySMTTranslator(language, self.static_symbols, anames)
            #print(f"theory: {theory}")
            translated = translator.translate(theory, horizon)
            #print(f"translated: {translated}")
            # Let's simplify the sentences for further clarity
            translated = [t.simplify() for t in translated]
            print_as_smtlib(translated,[], sys.stdout)
            model = solve(translated, 'z3')
            return model #decode_smt_model(model, horizon, translator)

    def effect_as_substitution(self, eff, substitution={}):
        # An add effect means identity substitution
        vart = _get_timestep_var(self.metalang)
        if isinstance(eff, fs.AddEffect):
            x_t = self.to_metalang(eff.atom, vart, subt=vart)
            substitution[symref(x_t)] = x_t
        elif isinstance(eff, fs.DelEffect):
            x_t = self.to_metalang(eff.atom, vart, subt=vart)
            substitution[symref(x_t)] = self.to_metalang(neg(x_t), vart, subt=vart)
        elif isinstance(eff, fs.FunctionalEffect):
            x_t = self.to_metalang(eff.lhs, vart, subt=vart)
            substitution[symref(x_t)] = self.to_metalang(eff.rhs, vart, subt=vart)
        else:
            print(f"What is {eff}? Baby don't hurt me!")

    def get_expression_bounds(self, expr):
        s = expr.sort
        # Note that bounds in Tarski intervals are inclusive, while here we expect an exclusive upper bound
        return (s.lower_bound, s.upper_bound + 1) if isinstance(s, Interval) else self.sort_bounds[s]

    def create_quantified_variable(self, v, lang):
        # First deal with the two unbound cases:
        if v.sort == lang.Integer:
            return Symbol(v.symbol, INT), TRUE()

        if v.sort == lang.Real:
            return Symbol(v.symbol, REAL), TRUE()

        # Otherwise assume we have a bounded type (including Enumerated types)
        smtvar = Symbol(v.symbol, INT)

        lb, up = self.get_expression_bounds(v)
        if lb >= up:
            raise TransformationError(f"SMT variable corresponding to sort '{v.sort}' has cardinality 0")

        bounds = And(GE(smtvar, Int(lb)), LT(smtvar, Int(up)))
        return smtvar, bounds

# auxiliary functions stolen from the lifted encoding file
def _get_timestep_sort(lang):
# Currently we use Real, as Natural gives some casting problems
# return lang.Timestep
# return lang.Natural
    return lang.Real

def generate_action_arguments(lang, act, char='z'):
    binding = [lang.variable(f"{char}{i}", lang.get_sort(v.sort.name)) for i, v in enumerate(act.parameters, start=1)]
    return binding

def _get_timestep_var(lang, name="t"):
    return lang.variable(name, _get_timestep_sort(lang))

def _get_timestep_const(lang, value):
    return Constant(value, _get_timestep_sort(lang)) if isinstance(value, int) else value

def _get_affected_atom(eff):
    """ Given an effect, it returns the predicate that is changed """
    return eff.atom if isinstance(eff, (fs.AddEffect, fs.DelEffect)) else eff.lhs


