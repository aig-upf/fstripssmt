import itertools
from collections import OrderedDict, defaultdict

import tarski.fstrips as fs
from tarski import Constant, Variable, Function
from tarski.syntax import symref, Sort, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    neg, Interval, Contradiction

import pysmt
from pysmt.shortcuts import FreshSymbol, Symbol, EqualsOrIff
from pysmt.shortcuts import Bool, Int, Real, FunctionType
from pysmt.shortcuts import LE, GE, Equals
from pysmt.shortcuts import And, Implies, Or, TRUE, FALSE, Not
from pysmt.typing import INT, BOOL, REAL
from tarski.syntax.sorts import parent

from fstripssmt.encodings.pysmt import get_pysmt_predicate, get_pysmt_connective
from fstripssmt.errors import TransformationError


class ClassicalEncoding(object):
    """ """

    def __init__(self, problem: fs.Problem, operators, statevars):
        self.problem = problem
        self.language = self.problem.language
        self.operators = operators
        self.statevars = statevars

        # A map from compound terms to corresponding state variables
        self.statevaridx = self._index_state_variables(statevars)

        self.interferences = self.compute_interferences()

        self.vars = OrderedDict()
        self.actionvars = OrderedDict()  # The boolean vars denoting application of an operator at a given timepoint
        self.b = OrderedDict()
        self.function_types = OrderedDict()
        self.function_terms = OrderedDict()

        # Axioms
        self.Init = []
        self.Goal = []
        self.Domains = []
        self.ActionPreconditions = []
        self.ActionEffects = []
        self.Persistence = []
        self.Interference = []
        self.Constraints = []

        self.custom_domain_terms = OrderedDict()

    @staticmethod
    def _index_state_variables(statevars):
        indexed = dict()
        for v in statevars:
            indexed[symref(v.to_atom())] = v
        return indexed

    def generate_theory(self, horizon):
        """ The main entry point to the class, generates the entire logical theory
        for a given horizon. """
        theory = []
        theory += self.initial_state()

        for h in range(horizon):
            for op in self.operators:
                theory += self.assert_operator(op, h)
            theory += self.assert_frame_axioms(h)
            theory += self.assert_interference_axioms(h)

        theory += self.goal(horizon)

        return theory

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

    def resolve_type_for_sort(self, s: Sort):
        if s == self.language.Integer:
            return INT
        elif s == self.language.Real:
            return REAL
        else:  # We'll model enumerated types as integers
            return INT

    def resolve_constant(self, c: Constant, sort: Sort = None):
        if not isinstance(c, Constant):
            raise TransformationError(f"Compilation of static (constant) terms like '{c}' not implemented yet!")

        if sort is None:
            sort = c.sort

        if sort == self.language.Integer:
            return Int(c.symbol)

        if sort == self.language.Real:
            return Real(c.symbol)

        if isinstance(sort, Interval):
            return self.resolve_constant(c, parent(sort))

        # Otherwise assume we have a enumerated type and simply return the index of the object
        for k, v in enumerate(sort.domain()):
            if v.symbol == c.symbol:
                return Int(k)
        raise RuntimeError(f"Don't know how to deal with sort '{sort}' for constant '{c}'")

    def create_enum_type_domain_axioms(self, y, sort):
        self.custom_domain_terms[y] = sort
        card = len(list(sort.domain()))
        if not card:
            raise TransformationError(f"Unexpected domain with cardinality 0: {sort}")
        self.Domains += [GE(y, Int(0)), LE(y, Int(card - 1))]

    def create_function_type(self, func: Function, t):

        domain_types = [self.resolve_type_for_sort(s) for s in func.domain]
        codomain_type = self.resolve_type_for_sort(func.codomain)

        func_type = FunctionType(codomain_type, domain_types)
        self.function_types[func.signature] = func_type
        self.function_terms[func.signature, t] = Symbol(func.signature, func_type)
        return self.function_terms[func.signature, t]

    def create_function_application_term(self, f: Function, args, t):
        assert False, "This code needs to be revised"
        try:
            func_term = self.function_terms[f.signature, t]
        except KeyError:
            if f.arity > 0:
                func_term = self.create_function_type(f, t)
                self.function_terms[f.signature, t] = func_term
            else:
                # MRJ: arity zero symbol maps directly to term
                x = Variable('{}@{}'.format(f.signature, t), f.codomain)
                assert False, "check what name should be given to var"
                func_term = self.create_variable(x)
                self.function_terms[f.signature, t] = func_term
                return func_term

        if f.arity == 0:
            return func_term
        return pysmt.shortcuts.Function(func_term, args)

    @staticmethod
    def create_bool_term(atom, name):
        return Symbol(name, BOOL)

    def create_variable(self, elem, sort=None, name=None):
        sort = elem.sort if sort is None else sort
        name = str(elem) if name is None else name

        if sort == self.language.Integer:
            return Symbol(name, INT)

        if sort == self.language.Real:
            return Symbol(name, REAL)

        if isinstance(sort, Interval):
            # Let's go seek the underlying type of the interval recursively!
            return self.create_variable(elem, parent(sort), name)

        # Otherwise assume we have a enumerated type and simply return the index of the object
        y_var = FreshSymbol(INT)
        self.create_enum_type_domain_axioms(y_var, elem.sort)
        return y_var

    def smt_nested_term(self, phi, t):
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
        theory = []
        for sv in self.statevars:
            x = sv.to_atom()
            if isinstance(x, Atom):
                atom = self.smt_variable(x, 0)
                theory.append(atom if self.problem.init[x] else Not(atom))
            elif isinstance(x, CompoundTerm):
                theory += [self.rewrite(x == self.problem.init[x], 0)]
            else:
                raise TransformationError(f'Cannot handle state variable "{sv}"')
        return theory

    def goal(self, t):
        return [self.rewrite(self.problem.goal, t)]

    def assert_operator(self, op, t):
        op_atom = self.smt_action(op, t)
        theory = [Implies(op_atom, self.rewrite(op.precondition, t))]
        for eff in op.effects:
            if isinstance(eff, fs.AddEffect):
                theory.append(Implies(op_atom, self.rewrite(eff.atom, t + 1)))
            elif isinstance(eff, fs.DelEffect):
                theory.append(Implies(op_atom, self.rewrite(neg(eff.atom), t + 1)))
            elif isinstance(eff, fs.LiteralEffect):
                theory.append(Implies(op_atom, self.rewrite(eff.lit, t + 1)))
            elif isinstance(eff, fs.FunctionalEffect):
                lhs = self.rewrite(eff.lhs, t + 1)
                rhs = self.rewrite(eff.rhs, t)
                theory.append(Implies(op_atom, Equals(lhs, rhs)))
            else:
                raise TransformationError(f"Can't compile effect {eff}")
        return theory

    def assert_frame_axioms(self, t):
        theory = []
        for x in self.statevars:
            atom = x.to_atom()
            x_t = self.smt_variable(atom, t)
            x_t1 = self.smt_variable(atom, t + 1)

            a_terms = [self.smt_action(op, t) for op in self.interferences[symref(atom)]]
            # x_t != x_{t+1}  =>  some action that affects x_t has been executed at time t
            # Note that this handles well the case where there is no such action: Or([])=False
            theory.append(Or(EqualsOrIff(x_t, x_t1), Or(a_terms)))

        return theory

    def assert_interference_axioms(self, t):
        theory = []
        for interfering in self.interferences.values():
            for op1, op2 in itertools.combinations(interfering, 2):
                theory.append(Or(Not(self.actionvars[op1.ident(), t]), Not(self.actionvars[op2.ident(), t])))
        return theory

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

        elif isinstance(phi, Atom):
            if phi.predicate.builtin:
                if len(phi.subterms) != 2:
                    raise TransformationError(f"Non-binary builtin atom {phi} not supported")
                lhs, rhs = [self.rewrite(psi, t) for psi in phi.subterms]
                return get_pysmt_predicate(phi.symbol.symbol)(lhs, rhs)
            return self.smt_variable(phi, t)

        elif isinstance(phi, CompoundTerm):
            if phi.symbol.builtin:
                if len(phi.subterms) != 2:
                    raise TransformationError(f"Non-binary built-in symbols now allowed ({phi})")
                lhs, rhs = [self.rewrite(psi, t) for psi in phi.subterms]
                return get_pysmt_predicate(phi.symbol.symbol)(lhs, rhs)

            if symref(phi) in self.statevaridx:
                # For a state variable, simply return the (possibly cached) variable corresponding to it
                return self.smt_variable(phi, t)

            return self.smt_nested_term(phi, t)

        elif isinstance(phi, Variable):
            return self.smt_variable(phi, t)

        elif isinstance(phi, Constant):
            return self.resolve_constant(phi)

        raise TransformationError(f"Don't know how to translate formula '{phi}'")

    def interpret_term(self, model, term):
        term_type = term.get_type()
        if term_type == BOOL or term_type == REAL or term_type == INT:
            return model[term]
        term_value = model[term]
        try:
            term_sort = self.custom_domain_terms[term]
            term_value = str(list(term_sort.domain())[term_value])
        except KeyError:
            pass
        return term_value

    def extract_plan(self, model):
        plan = OrderedDict()
        for idx, a in self.actionvars.items():
            act_name, t = idx
            i = self.interpret_term(model, a)
            if i.constant_value():
                try:
                    plan[t] += [(act_name, 1)]
                except KeyError:
                    plan[t] = [(act_name, 1)]
        for idx, b in self.b.items():
            act_name, t = idx
            i = self.interpret_term(model, b)
            if i.constant_value() > 0:
                try:
                    plan[t] += [(act_name, i.constant_value())]
                except KeyError:
                    plan[t] = [(act_name, i.constant_value())]

        return plan

    def decode_model(self):
        for idx, x in self.vars.items():
            symbol_ref, t = idx
            print('{}@{} = {}'.format(str(symbol_ref.expr), t, self.interpret_term(self.model, x)))
        for idx, a in self.actionvars.items():
            act_name, t = idx
            value = self.interpret_term(self.model, a)
            if value:
                print('{}@{}'.format(act_name, t))
        for idx, b in self.b.items():
            act_name, t = idx
            value = self.interpret_term(self.model, b)

            if value > 0:
                print('{}@{}={}'.format(act_name, t, value))
