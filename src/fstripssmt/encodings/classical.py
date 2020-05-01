import itertools
from collections import OrderedDict, defaultdict

import tarski
import tarski.fstrips as fs
from tarski import Constant, Variable, Function, Predicate
from tarski.fstrips import FunctionalEffect
from tarski.fstrips.representation import classify_atom_occurrences_in_formula
from tarski.syntax import symref, Sort, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Interval, Contradiction, term_substitution, forall, land, implies, lor, exists

import pysmt
from pysmt.shortcuts import FreshSymbol, Symbol, EqualsOrIff, Int, Real, FunctionType, And
from pysmt.shortcuts import LT, GE, Equals, Implies, Or, TRUE, FALSE, Not
from pysmt.typing import INT, BOOL, REAL
from tarski.syntax.ops import compute_sort_id_assignment, flatten
from tarski.syntax.sorts import parent, compute_signature_bindings
from tarski.syntax.util import get_symbols
from tarski.theories import has_theory

from .pysmt import get_pysmt_predicate, get_pysmt_connective
from ..errors import TransformationError
from ..nested import compile_nested_predicates_into_functions


class Theory:
    def __init__(self, encoding):
        self.encoding = encoding
        self.vars = dict()
        self.constraints = []


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

        # Compute a sort-contiguous object ID assignment
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.lang)
        # print(self.sort_bounds)
        # print(self.object_ids)

        # A map from compound terms to corresponding state variables
        self.statevaridx = _index_state_variables(statevars)

        self.interferences, self.mutexes = self.compute_interferences(self.operators)

        self.eff_index = analyze_action_effects(self.metalang, problem.actions.values())
        self.gamma_pos, self.gamma_neg, self.gamma_fun = self.compute_gammas(problem, self.metalang)

        self.vars = OrderedDict()
        self.actionvars = OrderedDict()  # The boolean vars denoting application of an operator at a given timepoint
        self.function_types = OrderedDict()  # TODO Not sure this will be needed
        self.function_terms = OrderedDict()

        self.custom_domain_terms = OrderedDict()
        self.mtheory = []
        self.theory = None

    @staticmethod
    def setup_metalang(problem):
        """ Set up the Tarski metalanguage where we will build the SMT compilation """
        lang = problem.language
        ml = tarski.fstrips.language(f"{lang.name}-smt", theories=["equality", "arithmetic"])

        # Declare all sorts
        for s in lang.sorts:
            if not s.builtin and s.name != "object":
                ml.sort(s.name, parent(s).name)

        # Declare an extra "timestep" sort. Note: ATM Just using unbounded Natural objects
        # ts_t = ml.interval("timestep", _get_timestep_sort(ml))

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
        self.theory = Theory(self)  # This will overwrite previous Theory objects, if any, and start from scratch
        self.assert_initial_state()
        self.goal(horizon)

        self.assert_frame_axioms()
        self.assert_interference_axioms()

        for a in self.problem.actions.values():
            self.assert_operator(a)

        return self.mtheory

    def is_state_variable(self, expression):
        return symref(expression) in self.statevaridx

    def compute_interferences(self, operators):
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

    def resolve_type_for_sort(self, s):
        if has_theory(self.lang, "arithmetic") and s == self.lang.Integer:
            return INT
        elif has_theory(self.lang, "arithmetic") and s == self.lang.Real:
            return REAL
        elif s is bool:
            return BOOL
        else:  # We'll model enumerated types as integers
            return INT

    def resolve_constant(self, c: Constant, sort: Sort = None):
        if sort is None:
            sort = c.sort

        if has_theory(self.lang, "arithmetic") and sort == self.lang.Integer:
            return Int(c.symbol)

        if has_theory(self.lang, "arithmetic") and sort == self.lang.Real:
            return Real(c.symbol)

        if isinstance(sort, Interval):
            return self.resolve_constant(c, parent(sort))

        # Otherwise we must have an enumerated type and simply return the object ID
        return Int(self.object_ids[symref(c)])

    def create_enum_type_domain_axioms(self, y, sort):
        self.custom_domain_terms[y] = sort
        lb, up = self.sort_bounds[sort]
        if lb >= up:
            raise TransformationError(f"Found SMT variable corresponding to domain (of sort '{sort}')"
                                      f"with cardinality 0")

        self.theory.constraints += [GE(y, Int(lb)), LT(y, Int(up))]

    def create_function_type(self, fun: Function, t):
        assert fun.arity > 0  # Otherwise this would be a state variable
        domain_types = [self.resolve_type_for_sort(s) for s in fun.domain]
        # codomain = func.codomain if isinstance(func, Function) else self.resolve_type_for_sort(func.language.Boolean)
        codomain = fun.codomain if isinstance(fun, Function) else bool
        codomain_type = self.resolve_type_for_sort(codomain)
        funtype = FunctionType(codomain_type, domain_types)
        return Symbol(f"{fun.name}@{t}", funtype), funtype

    def create_function_application_term(self, fun: Function, args, t):
        """ """
        try:
            fun_term = self.function_terms[fun.signature, t]
        except KeyError:
            fun_term, funtype = self.create_function_type(fun, t)
            self.function_terms[fun.signature, t] = fun_term
            self.function_types[fun.signature] = funtype

        return pysmt.shortcuts.Function(fun_term, args)

    @staticmethod
    def create_bool_term(atom, name):
        return Symbol(name, BOOL)

    def create_variable(self, elem, sort=None, name=None):
        sort = elem.sort if sort is None else sort
        name = str(elem) if name is None else name

        if has_theory(self.lang, "arithmetic") and sort == self.lang.Integer:
            return Symbol(name, INT)

        if has_theory(self.lang, "arithmetic") and sort == self.lang.Real:
            return Symbol(name, REAL)

        if isinstance(sort, Interval):
            # Let's go seek the underlying type of the interval recursively!
            return self.create_variable(elem, parent(sort), name)

        # Otherwise assume we have a enumerated type and simply return the index of the object
        y_var = Symbol(name, INT)
        self.create_enum_type_domain_axioms(y_var, elem.sort)
        return y_var

    def smt_nested_expression(self, phi, t, subt=None):
        subt = t if subt is None else subt
        key = (symref(phi), t, subt)
        try:
            return self.vars[key]
        except KeyError:
            params = [self.rewrite(st, subt) for st in phi.subterms]
            self.vars[key] = res = self.create_function_application_term(phi.symbol, params, t)
        return res

    def smt_variable(self, expr, timepoint):
        """ Return the (possibly cached) SMT theory variable that corresponds to the given Tarski
        logical expression, which can be either an atom (e.g. clear(b1)) or a compound term representing
        a state variable (e.g. value(c1)). """
        assert isinstance(expr, (Atom, CompoundTerm, Variable))
        key = (symref(expr), timepoint)
        try:
            return self.vars[key]
        except KeyError:
            creator = self.create_bool_term if isinstance(expr, Atom) else self.create_variable
            self.vars[key] = res = creator(expr, name=f'{expr}@{timepoint}')
        return res

    def smt_action(self, action, timepoint):
        key = (action.ident(), timepoint)
        try:
            return self.actionvars[key]
        except KeyError:
            self.actionvars[key] = res = self.create_bool_term(action, name=f'{action.ident()}@{timepoint}')
        return res

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

    def assert_operator(self, op):
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
        a_implies_prec = forall(*vars_, implies(happens, self.to_metalang(prec, vart)))
        self.mtheory.append(a_implies_prec)

        for eff in op.effects:
            eff = term_substitution(eff, substitution)
            antec = happens
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
            self.mtheory.append(a_implies_eff)

    def assert_frame_axioms(self):
        ml = self.metalang
        tvar = _get_timestep_var(ml)

        # First deal with predicates;
        for p in get_symbols(self.lang, type_="predicate", include_builtin=False):
            lvars = generate_symbol_arguments(self.lang, p)
            atom = p(*lvars)

            # pos: not p(x, t) and p(x, t+1)  => \gamma^+_(x, t)
            # neg: p(x, t) and not p(x, t+1)  => \gamma^-_(x, t)
            at_t = self.to_metalang(atom, tvar)
            at_t1 = self.to_metalang(atom, tvar + 1)
            mlvars = generate_symbol_arguments(ml, p)
            pos = forall(*mlvars, implies(~at_t & at_t1, self.gamma_pos[p.name]))
            neg = forall(*mlvars, implies(at_t & ~at_t1, self.gamma_neg[p.name]))
            self.mtheory += [pos, neg]

        # Now deal with functions:
        for p in get_symbols(self.lang, type_="function", include_builtin=False):
            lvars = generate_symbol_arguments(self.lang, p)
            atom = p(*lvars)

            # fun: f(x, t) != y and f(x, t+1) = y   => \gamma^+_(x, t)
            yvar = ml.variable("y", ml.get_sort(p.codomain.name))
            at_t = self.to_metalang(atom, tvar) != yvar
            at_t1 = self.to_metalang(atom, tvar+1) == yvar
            mlvars = generate_symbol_arguments(ml, p) + [yvar]
            fun = forall(*mlvars, implies(at_t & at_t1, self.gamma_fun[p.name]))
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


    # def assert_interference_axioms(self, t):
    #     for interfering in self.interferences.values():
    #         for op1, op2 in itertools.combinations(interfering, 2):
    #             self.theory.constraints.append(Or(Not(self.actionvars[op1.ident(), t]),
    #             Not(self.actionvars[op2.ident(), t])))


    def timestep(self, t):
        return Constant(t, _get_timestep_sort(self.metalang)) if isinstance(t, int) else t

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
                args += (self.timestep(t),)

            return CompoundTerm(ml.get_function(phi.symbol.name), args)

        elif isinstance(phi, Atom):
            # TODO Deal with non-fluent symbols, which won't need the timestep argument
            args = tuple(self.to_metalang(psi, subt) for psi in phi.subterms)
            if self.symbol_is_fluent(phi.symbol):
                args += (self.timestep(t),)
            return Atom(ml.get_predicate(phi.symbol.name), args)

        raise TransformationError(f"Don't know how to transform element or expression '{phi}' to the SMT metalanguage")

    def rewrite(self, phi, t, subt=None):
        subt = t if subt is None else subt
        if isinstance(phi, QuantifiedFormula):
            raise TransformationError(f"Don't know how to deal with quantified formula {phi}")

        elif isinstance(phi, Tautology):
            return TRUE()

        elif isinstance(phi, Contradiction):
            return FALSE()

        elif isinstance(phi, CompoundFormula):
            pysmt_fun = get_pysmt_connective(phi.connective)
            return pysmt_fun(*(self.rewrite(psi, subt) for psi in phi.subformulas))

        elif isinstance(phi, (Atom, CompoundTerm)):
            if phi.symbol.builtin:
                if len(phi.subterms) != 2:
                    raise TransformationError(f"Unsupported non-binary builtin expression {phi}")
                lhs, rhs = (self.rewrite(psi, subt) for psi in phi.subterms)
                return get_pysmt_predicate(phi.symbol.symbol)(lhs, rhs)

            if phi.symbol in self.nested_symbols:
                # Even if phi is a state variable, if its head symbol appears nested elsewhere, we'll need to deal
                # with it as an uninterpreted function
                return self.smt_nested_expression(phi, t, subt)
            
            elif self.is_state_variable(phi):
                # For a state variable, simply return the (possibly cached) variable corresponding to it
                return self.smt_variable(phi, t)
            
            return self.smt_nested_expression(phi, t, subt)

        elif isinstance(phi, Variable):
            return self.smt_variable(phi, t)

        elif isinstance(phi, Constant):
            return self.resolve_constant(phi)

        raise TransformationError(f"Don't know how to translate formula '{phi}'")

    def interpret_term(self, model, term):
        term_type = term.get_type()
        if term_type in (BOOL, REAL, INT):
            return model[term]
        term_value = model[term]
        try:
            assert 0, "revise this"
            term_sort = self.custom_domain_terms[term]
            term_value = str(list(term_sort.domain())[term_value])
        except KeyError:
            pass
        return term_value

    def extract_parallel_plan(self, model):
        plan = defaultdict(list)
        for (aname, t), a in self.actionvars.items():
            val = self.interpret_term(model, a)
            if val.constant_value():
                plan[t] += [aname]
        return plan

    def decode_model(self, model):
        for (sref, t), x in self.vars.items():
            print(f'{sref.expr}@{t} = {self.interpret_term(model, x)}')

        for (aname, t), a in self.actionvars.items():
            val = self.interpret_term(model, a)
            if val.constant_value():
                print('{}@{}'.format(aname, t))


def bool_to_tarski_boolean(lang, value):
    assert isinstance(value, bool)
    return lang.get("True" if value else "False")


def bool_to_pysmt_boolean(value):
    assert isinstance(value, bool)
    return TRUE() if value else FALSE()


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
    return lang.Real


def _get_timestep_var(lang, name="t"):
    return lang.variable(name, _get_timestep_sort(lang))


def linearize_parallel_plan(plan):
    timesteps = sorted(plan.keys())
    return list(itertools.chain.from_iterable(plan[t] for t in timesteps))

