import itertools
from collections import OrderedDict, defaultdict

import tarski.fstrips as fs
from tarski import Constant, Variable, Function
from tarski.syntax import symref, Sort, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    neg, Interval, Contradiction

import pysmt
from pysmt.shortcuts import FreshSymbol, Symbol, EqualsOrIff, Int, Real, FunctionType
from pysmt.shortcuts import LT, GE, Equals, Implies, Or, TRUE, FALSE, Not
from pysmt.typing import INT, BOOL, REAL
from tarski.syntax.ops import compute_sort_id_assignment
from tarski.syntax.sorts import parent
from tarski.theories import has_theory

from fstripssmt.encodings.pysmt import get_pysmt_predicate, get_pysmt_connective
from fstripssmt.errors import TransformationError


class Theory:
    def __init__(self, encoding):
        self.encoding = encoding
        self.vars = dict()
        self.constraints = []


class ClassicalEncoding:
    """ """

    def __init__(self, problem: fs.Problem, operators, statevars):
        self.problem = problem
        self.language = self.problem.language
        self.operators = operators
        self.statevars = statevars

        # Compute a sort-contiguous object ID assignment
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.language)
        print(self.sort_bounds)
        print(self.object_ids)

        # A map from compound terms to corresponding state variables
        self.statevaridx = self._index_state_variables(statevars)

        self.interferences = self.compute_interferences()

        self.vars = OrderedDict()
        self.actionvars = OrderedDict()  # The boolean vars denoting application of an operator at a given timepoint
        self.function_types = OrderedDict()
        self.function_terms = OrderedDict()

        self.custom_domain_terms = OrderedDict()

        self.theory = None

    @staticmethod
    def _index_state_variables(statevars):
        indexed = dict()
        for v in statevars:
            indexed[symref(v.to_atom())] = v
        return indexed

    def generate_theory(self, horizon):
        """ The main entry point to the class, generates the entire logical theory
        for a given horizon. """
        self.theory = Theory(self)  # This will overwrite previous Theory objects, if any, and start from scratch
        self.initial_state()

        for h in range(horizon):
            for op in self.operators:
                self.assert_operator(op, h)
            self.assert_frame_axioms(h)
            self.assert_interference_axioms(h)

        self.goal(horizon)

        return self.theory

    def compute_interferences(self):
        interferences = defaultdict(list)
        for ops in self.operators:
            for eff in ops.effects:
                if isinstance(eff, (fs.AddEffect, fs.DelEffect)):
                    interferences[symref(eff.atom)].append(ops)
                elif isinstance(eff, fs.FunctionalEffect):
                    interferences[symref(eff.lhs)].append(ops)
                else:
                    raise TransformationError(f'Cannot handle effect "{eff}"')
        return interferences

    def resolve_type_for_sort(self, s):
        if has_theory(self.language, "arithmetic") and s == self.language.Integer:
            return INT
        elif has_theory(self.language, "arithmetic") and s == self.language.Real:
            return REAL
        elif isinstance(s, bool):
            return BOOL
        else:  # We'll model enumerated types as integers
            return INT

    def resolve_constant(self, c: Constant, sort: Sort = None):
        if not isinstance(c, Constant):
            raise TransformationError(f"Compilation of static (constant) terms like '{c}' not implemented yet!")

        if sort is None:
            sort = c.sort

        if has_theory(self.language, "arithmetic") and sort == self.language.Integer:
            return Int(c.symbol)

        if has_theory(self.language, "arithmetic") and sort == self.language.Real:
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

    def create_function_type(self, func: Function, t):
        domain_types = [self.resolve_type_for_sort(s) for s in func.domain]
        codomain_type = self.resolve_type_for_sort(func.codomain) if isinstance(func, Function) else bool

        func_type = FunctionType(codomain_type, domain_types)
        self.function_types[func.signature] = func_type
        self.function_terms[func.signature, t] = Symbol(func.signature, func_type)
        return self.function_terms[func.signature, t]

    def create_function_application_term(self, f: Function, args, t):
        # assert False, "This code needs to be revised"
        try:
            func_term = self.function_terms[f.signature, t]
        except KeyError:
            assert f.arity > 0
            func_term = self.create_function_type(f, t)
            self.function_terms[f.signature, t] = func_term
        return pysmt.shortcuts.Function(func_term, args)

    @staticmethod
    def create_bool_term(atom, name):
        return Symbol(name, BOOL)

    def create_variable(self, elem, sort=None, name=None):
        sort = elem.sort if sort is None else sort
        name = str(elem) if name is None else name

        if has_theory(self.language, "arithmetic") and sort == self.language.Integer:
            return Symbol(name, INT)

        if has_theory(self.language, "arithmetic") and sort == self.language.Real:
            return Symbol(name, REAL)

        if isinstance(sort, Interval):
            # Let's go seek the underlying type of the interval recursively!
            return self.create_variable(elem, parent(sort), name)

        # Otherwise assume we have a enumerated type and simply return the index of the object
        y_var = Symbol(name, INT)
        self.create_enum_type_domain_axioms(y_var, elem.sort)
        return y_var

    def smt_nested_expression(self, phi, t):
        key = (symref(phi), t)
        try:
            return self.vars[key]
        except KeyError:
            params = [self.rewrite(st, t) for st in phi.subterms]
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

    def initial_state(self):
        for sv in self.statevars:
            x = sv.to_atom()
            if isinstance(x, Atom):
                atom = self.smt_variable(x, 0)
                self.theory.constraints.append(atom if self.problem.init[x] else Not(atom))
            elif isinstance(x, CompoundTerm):
                self.theory.constraints += [self.rewrite(x == self.problem.init[x], 0)]
            else:
                raise TransformationError(f'Cannot handle state variable "{sv}"')

    def goal(self, t):
        self.theory.constraints.append(self.rewrite(self.problem.goal, t))

    def assert_operator(self, op, t):
        """ For given operator op and timestep t, assert the SMT expression:
                op@t --> op.precondition@t
                op@t --> op.effects@(t+1)
        """
        op_atom = self.smt_action(op, t)
        self.theory.constraints += [Implies(op_atom, self.rewrite(op.precondition, t))]
        for eff in op.effects:
            if isinstance(eff, fs.AddEffect):
                self.theory.constraints.append(Implies(op_atom, self.rewrite(eff.atom, t + 1)))
            elif isinstance(eff, fs.DelEffect):
                self.theory.constraints.append(Implies(op_atom, self.rewrite(neg(eff.atom), t + 1)))
            elif isinstance(eff, fs.FunctionalEffect):
                lhs = self.rewrite(eff.lhs, t + 1)
                rhs = self.rewrite(eff.rhs, t)
                self.theory.constraints.append(Implies(op_atom, Equals(lhs, rhs)))
            else:
                raise TransformationError(f"Can't compile effect {eff}")

            if not isinstance(eff.condition, Tautology):
                raise TransformationError(f"Current compilation not yet ready for conditional effects such as {eff}")

    def assert_frame_axioms(self, t):
        for x in self.statevars:
            atom = x.to_atom()
            x_t = self.smt_variable(atom, t)
            x_t1 = self.smt_variable(atom, t + 1)

            a_terms = [self.smt_action(op, t) for op in self.interferences[symref(atom)]]
            # x_t != x_{t+1}  =>  some action that affects x_t has been executed at time t
            # Note that this handles well the case where there is no such action: Or([])=False
            self.theory.constraints.append(Or(EqualsOrIff(x_t, x_t1), Or(a_terms)))

    def assert_interference_axioms(self, t):
        for interfering in self.interferences.values():
            for op1, op2 in itertools.combinations(interfering, 2):
                self.theory.constraints.append(Or(Not(self.actionvars[op1.ident(), t]), Not(self.actionvars[op2.ident(), t])))

    def rewrite(self, phi, t):
        if isinstance(phi, QuantifiedFormula):
            raise TransformationError(f"Don't know how to deal with quantified formula {phi}")

        elif isinstance(phi, Tautology):
            return TRUE()

        elif isinstance(phi, Contradiction):
            return FALSE()

        elif isinstance(phi, CompoundFormula):
            pysmt_fun = get_pysmt_connective(phi.connective)
            return pysmt_fun(*(self.rewrite(psi, t) for psi in phi.subformulas))

        elif isinstance(phi, (Atom, CompoundTerm)):
            if phi.symbol.builtin:
                if len(phi.subterms) != 2:
                    raise TransformationError(f"Unsupported non-binary builtin expression {phi}")
                lhs, rhs = (self.rewrite(psi, t) for psi in phi.subterms)
                return get_pysmt_predicate(phi.symbol.symbol)(lhs, rhs)
            
            if symref(phi) in self.statevaridx:
                # For a state variable, simply return the (possibly cached) variable corresponding to it
                return self.smt_variable(phi, t)
            
            return self.smt_nested_expression(phi, t)

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


def linearize_parallel_plan(plan):
    timesteps = sorted(plan.keys())
    return list(itertools.chain.from_iterable(plan[t] for t in timesteps))
