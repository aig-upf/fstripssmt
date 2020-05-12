import copy
import sys

from multipledispatch import dispatch

#from fstripssmt.runner import decode_smt_model
from fstripssmt.solvers.common import solve
from .solvers.pysmt import PySMTTranslator, print_as_smtlib
from .errors import TransformationError

import tarski
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

        # Declare an extra "timestep" sort. Note: ATM Just using unbounded Natural objects
        # ml.Timestep = ml.interval("timestep", _get_timestep_sort(ml), 0, 5)
        # ml.Timestep = ml.interval("timestep", ml.Real, 0, 5)

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
        """ parameters:
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
        # Don't use the timestep arg
        vars_ = generate_action_arguments(ml, a, char='a') + generate_action_arguments(ml, b, char='b')
        vart = _get_timestep_var(ml)
        args = vars_ + [vart]
        print(args)

        for a_eff in a.effects:
            for b_eff in b.effects:
                print(f"lets check if effects \n\t action a:{a} --- effect:{a_eff} \n\t action b:{b} --- effect:{b_eff} \n are simply commuting:")
                # substitute the parameters on the effects
                vars_a, translated_a = self.get_translated_effect(a, a_eff, 'a_')
                vars_b, translated_b = self.get_translated_effect(b, b_eff, 'b_')

                # TODO: substitution one on another

                # lets check if not (sigma_a = sigma_b) is T - satisfiable
                # construct the problem and ask the SMT solver if SAT, break, else continue searching
                total_args = vars_a + vars_b + [_get_timestep_var(ml)]
                theory = [forall(*total_args, neg(equiv(translated_a,translated_b)))]

                model = self.solve_theory(theory)
                if model:
                    print("SAT, this means that they are NOT simply commuting")
                    print(model)
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
        return vars_, trans_eff

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

    def solve_theory(self, theory):
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
            translator = PySMTTranslator(self.metalang, self.static_symbols, anames)
            translated = translator.translate(theory, horizon)
            # Let's simplify the sentences for further clarity
            translated = [t.simplify() for t in translated]
            print_as_smtlib(translated,[], sys.stdout)
            model = solve(translated, 'z3')
            return model #decode_smt_model(model, horizon, translator)

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
