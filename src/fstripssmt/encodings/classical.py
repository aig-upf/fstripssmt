import itertools
from collections import OrderedDict, defaultdict

import tarski
import tarski.fstrips as fs
from tarski.fstrips import FunctionalEffect
from tarski.fstrips.representation import classify_atom_occurrences_in_formula
from tarski.syntax import symref, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Contradiction, term_substitution, forall, land, implies, lor, exists, Constant, Variable, Predicate
from tarski.syntax.ops import flatten
from tarski.syntax.sorts import parent, compute_signature_bindings
from tarski.syntax.util import get_symbols

from ..errors import TransformationError


class ClassicalEncoding:
    """ """

    def __init__(self, problem: fs.Problem, operators, statevars):
        self.lang = problem.language
        self.metalang = self.setup_metalang(problem)

        # Let's first check which symbols appear in the head of a nested term or predicate, e.g.
        # in expressions such as clear(loc(b1)), or health(target(gun2)).
        # We'll pretend all symbols are nested so as to use UF with them
        self.nested_symbols = set(get_symbols(self.lang, type_="all", include_builtin=False))
        # self.problem, _ = compile_nested_predicates_into_functions(problem)
        self.problem = problem

        self.operators = operators
        self.statevars = statevars

        # A map from compound terms to corresponding state variables
        self.statevaridx = _index_state_variables(statevars)

        self.interferences, self.mutexes = self.compute_interferences(self.operators)

        self.eff_index = analyze_action_effects(self.metalang, problem.actions.values())
        self.gamma_pos, self.gamma_neg, self.gamma_fun = self.compute_gammas(problem, self.metalang)

        self.vars = OrderedDict()
        self.actionvars = OrderedDict()  # The boolean vars denoting application of an operator at a given timepoint

        self.custom_domain_terms = OrderedDict()
        self.mtheory = []

    @staticmethod
    def setup_metalang(problem):
        """ Set up the Tarski metalanguage where we will build the SMT compilation. """
        lang = problem.language
        ml = tarski.fstrips.language(f"{lang.name}-smt", theories=["equality", "arithmetic"])

        # Declare all sorts
        for s in lang.sorts:
            if not s.builtin and s.name != "object":
                ml.sort(s.name, parent(s).name)

        # Declare an extra "timestep" sort. Note: ATM Just using unbounded Natural objects
        # ml.Timestep = ml.interval("timestep", _get_timestep_sort(ml), 0, 5)
        # ml.Timestep = ml.interval("timestep", ml.Real, 0, 5)

        # Declare all objects in the metalanguage
        for o in lang.constants():
            ml.constant(o.symbol, o.sort.name)

        # Declare all symbols
        for s in get_symbols(lang, type_="all", include_builtin=False):
            # TODO Deal with non-fluent symbols, which won't need the timestep argument
            if isinstance(s, Predicate):
                sort = [t.name for t in s.sort] + [_get_timestep_sort(ml)]
                ml.predicate(s.name, *sort)
            else:
                sort = [t.name for t in s.domain] + [_get_timestep_sort(ml)] + [s.codomain.name]
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
            gamma_act = exists(*action_binding, land(action_happens_at_t, effcond, *gamma_binding, flat=True))
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
        self.mtheory.append("Initial State")
        self.assert_initial_state()

        self.mtheory.append("Goal condition")
        self.goal(horizon)

        self.assert_frame_axioms()

        self.mtheory.append("Interference axioms")
        self.assert_interference_axioms()

        for a in self.problem.actions.values():
            self.mtheory.append(f"Precondition and effects of action {a}")
            self.assert_action(a)

        return self.metalang, self.mtheory

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
        # TODO Deal with non-fluent symbols appropriately
        for p in get_symbols(self.lang, type_="predicate", include_builtin=False):
            for binding in compute_signature_bindings(p.sort):
                atom = p(*binding)
                x = atom if self.problem.init[atom] else ~atom
                self.mtheory.append(self.to_metalang(x, 0))

        for f in get_symbols(self.lang, type_="function", include_builtin=False):
            for binding in compute_signature_bindings(f.domain):
                term = f(*binding)
                self.mtheory.append(self.to_metalang(term == self.problem.init[term], 0))

    def goal(self, t):
        self.mtheory.append(self.to_metalang(self.problem.goal, t))

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
        self.mtheory.append(a_implies_prec)

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
            self.mtheory.append(forall(*args, a_implies_eff))

    def assert_frame_axioms(self):
        ml = self.metalang
        tvar = _get_timestep_var(ml)

        # First deal with predicates;
        for p in get_symbols(self.lang, type_="all", include_builtin=False):
            self.mtheory.append(f"Frame axiom for symbol {p}")
            lvars = generate_symbol_arguments(self.lang, p)
            atom = p(*lvars)

            if isinstance(p, Predicate):
                # pos: not p(x, t) and p(x, t+1)  => \gamma^+_(x, t)
                # neg: p(x, t) and not p(x, t+1)  => \gamma^-_(x, t)
                at_t = self.to_metalang(atom, tvar)
                at_t1 = self.to_metalang(atom, tvar + 1)
                quant = generate_symbol_arguments(ml, p) + [tvar]
                pos = forall(*quant, implies(~at_t & at_t1, self.gamma_pos[p.name]))
                neg = forall(*quant, implies(at_t & ~at_t1, self.gamma_neg[p.name]))
                self.mtheory += [pos, neg]
            else:
                # fun: f(x, t) != y and f(x, t+1) = y   => \gamma^=_(x, y, t)
                yvar = ml.variable("y", ml.get_sort(p.codomain.name))
                at_t = self.to_metalang(atom, tvar) != yvar
                at_t1 = self.to_metalang(atom, tvar+1) == yvar
                quant = generate_symbol_arguments(ml, p) + [yvar] + [tvar]
                fun = forall(*quant, implies(at_t & at_t1, self.gamma_fun[p.name]))
                self.mtheory += [fun]

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
                x_neq_y = land(*(x != y for x, y in zip(a1_args, a2_args)), flat=True)
                sentence = implies(x_neq_y, sentence)
            self.mtheory += [forall(*allargs, sentence)]

    def symbol_is_fluent(self, symbol):
        # TODO This needs to be improved
        return not symbol.builtin

    def to_metalang(self, phi, t, subt=None):
        ml = self.metalang
        subt = t if subt is None else subt

        if isinstance(phi, QuantifiedFormula):
            raise TransformationError(f"Compilation of quantified formula {phi} not yet implemented")

        elif isinstance(phi, (Tautology, Contradiction)):
            return phi

        elif isinstance(phi, Variable):
            return ml.variable(phi.symbol, phi.sort.name)

        elif isinstance(phi, Constant):
            return ml.get_constant(phi.name)

        elif isinstance(phi, CompoundFormula):
            return CompoundFormula(phi.connective, tuple(self.to_metalang(psi, t) for psi in phi.subformulas))

        elif isinstance(phi, CompoundTerm):
            # TODO Deal with non-fluent symbols, which won't need the timestep argument
            args = tuple(self.to_metalang(psi, subt) for psi in phi.subterms)
            if self.symbol_is_fluent(phi.symbol):
                args += (_get_timestep_const(ml, t),)

            return CompoundTerm(ml.get_function(phi.symbol.name), args)

        elif isinstance(phi, Atom):
            # TODO Deal with non-fluent symbols, which won't need the timestep argument
            args = tuple(self.to_metalang(psi, subt) for psi in phi.subterms)
            if self.symbol_is_fluent(phi.symbol):
                args += (_get_timestep_const(ml, t),)
            return Atom(ml.get_predicate(phi.symbol.name), args)

        raise TransformationError(f"Don't know how to transform element or expression '{phi}' to the SMT metalanguage")


def bool_to_tarski_boolean(lang, value):
    assert isinstance(value, bool)
    return lang.get("True" if value else "False")


def _index_state_variables(statevars):
    indexed = dict()
    for v in statevars:
        indexed[symref(v.to_atom())] = v
    return indexed


def generate_symbol_arguments(lang, symbol, include_codomain=True, c='x'):
    return [lang.variable(f"{c}{i}", lang.get_sort(s.name)) for i, s in enumerate(symbol.domain, start=1)]


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
    # Currently we use Real, as Natural gives some casting problems
    # return lang.Timestep
    # return lang.Natural
    return lang.Real


def _get_timestep_var(lang, name="t"):
    return lang.variable(name, _get_timestep_sort(lang))


def _get_timestep_const(lang, value):
    return Constant(value, _get_timestep_sort(lang)) if isinstance(value, int) else value

