import itertools
from collections import OrderedDict, defaultdict

import tarski.fstrips as fs
from tarski import Constant, Term, Variable, Function
from tarski.evaluators.simple import evaluate
from tarski.syntax import symref, Sort, Connective, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    neg

import pysmt
from pysmt.shortcuts import FreshSymbol, Symbol, Iff
from pysmt.shortcuts import Bool, Int, Real, FunctionType
from pysmt.shortcuts import LE, GE, Equals
from pysmt.shortcuts import And, Implies, Or, TRUE, FALSE, Not
from pysmt.typing import INT, BOOL, REAL

from fstripssmt.encodings.pysmt import get_pysmt_predicate, get_pysmt_connective
from fstripssmt.errors import TransformationError


class ClassicalEncoding(object):
    """ """

    def __init__(self, problem: fs.Problem, operators, statevars):
        self.problem = problem
        self.language = self.problem.language
        self.operators = operators
        self.statevars = statevars
        self.problem.init.evaluator = evaluate

        self.interferences = self.compute_interferences()

        self.vars = OrderedDict()
        self.a = OrderedDict()
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

    def generate_theory(self, horizon):
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
        else:
            return INT

    def resolve_constant(self, phi: Term, target_sort: Sort = None):
        if not isinstance(phi, Constant):
            msg = "springroll.Theory: Compilation of static (constant) terms like '{}' not implemented yet!".format(
                str(phi))
            raise CompilationError(msg)
        if target_sort is None:
            target_sort = phi.sort
        if target_sort == self.language.Integer:
            return Int(phi.symbol)
        elif target_sort == self.language.Real:
            return Real(phi.symbol)
        domain = list(target_sort.domain())
        for k, v in enumerate(domain):
            if v.symbol == phi.symbol:
                return Int(k)
        return None

    def create_domain_axioms(self, y, sort):
        self.custom_domain_terms[y] = sort
        lb = Int(0)
        ub = Int(len(list(sort.domain())) - 1)
        # print('{} <= {} <= {}'.format(lb, xi, ub))
        self.Domains += [GE(y, lb), LE(y, ub)]

    def create_function_type(self, func: Function, t):

        domain_types = [self.resolve_type_for_sort(s) for s in func.domain]
        codomain_type = self.resolve_type_for_sort(func.codomain)

        func_type = FunctionType(codomain_type, domain_types)
        self.function_types[func.signature] = func_type
        self.function_terms[func.signature, t] = Symbol(func.signature, func_type)
        return self.function_terms[func.signature, t]

    def create_function_application_term(self, f: Function, args, t):
        try:
            func_term = self.function_terms[f.signature, t]
        except KeyError:
            if f.arity > 0:
                func_term = self.create_function_type(f, t)
                self.function_terms[f.signature, t] = func_term
            else:
                # MRJ: arity zero symbol maps directly to term
                x = Variable('{}@{}'.format(f.signature, t), f.codomain)
                func_term = self.create_variable(x)
                self.function_terms[f.signature, t] = func_term
                return func_term

        if f.arity == 0:
            return func_term
        return pysmt.shortcuts.Function(func_term, args)

    def create_bool_term(self, name=None):
        return FreshSymbol(BOOL) if name is None else Symbol(name, BOOL)

    def create_int_term(self):
        return FreshSymbol(INT)

    def create_variable(self, elem):
        if elem.sort == self.language.Integer:
            return FreshSymbol(INT)
        elif elem.sort == self.language.Real:
            return FreshSymbol(REAL)
        else:
            y_var = FreshSymbol(INT)
            self.create_domain_axioms(y_var, elem.sort)
            return y_var

    def xt(self, term, timepoint):
        try:
            xt = self.vars[symref(term), timepoint]
        except KeyError:
            xt = self.create_variable(term)
            self.vars[symref(term), timepoint] = xt
        return xt

    def smt_atom(self, atom, timepoint):
        """ """
        key = (symref(atom), timepoint)
        if key not in self.vars:
            self.vars[key] = self.create_bool_term(f'{atom}@{timepoint}')
        return self.vars[key]

    def smt_action(self, action, timepoint):
        key = (action.ident(), timepoint)
        if key not in self.a:
            self.a[key] = self.create_bool_term(f'{action.ident()}@{timepoint}')
        return self.a[key]

    def initial_state(self):
        theory = []
        for sv in self.statevars:
            x = sv.to_atom()
            if isinstance(x, Atom):
                atom = self.smt_atom(x, 0)
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
            x_t = self.smt_atom(atom, t)
            x_t1 = self.smt_atom(atom, t + 1)

            a_terms = [self.smt_action(op, t) for op in self.interferences[symref(atom)]]
            # x_t != x_{t+1}  =>  some action that affects x_t has been executed at time t
            # Note that this handles well the case where there is no such action: Or([])=False
            theory.append(Or(Iff(x_t, x_t1), Or(a_terms)))

        return theory

    def assert_interference_axioms(self, t):
        theory = []
        for interfering in self.interferences.values():
            for op1, op2 in itertools.combinations(interfering, 2):
                theory.append(Or(Not(self.a[op1.ident(), t]), Not(self.a[op2.ident(), t])))
        return theory

    def rewrite(self, phi, t):
        if isinstance(phi, QuantifiedFormula):
            raise TransformationError(f"Don't know how to deal with quantified formula {phi}")

        elif isinstance(phi, Tautology):
            return TRUE()

        elif isinstance(phi, CompoundFormula):
            pysmt_fun = get_pysmt_connective(phi.connective)
            if phi.connective == Connective.Not:
                return pysmt_fun(self.rewrite(phi.subformulas[0], t))
            return pysmt_fun(*(self.rewrite(psi, t) for psi in phi.subformulas))

        elif isinstance(phi, Atom):
            if phi.predicate.builtin:
                y_sub = [self.rewrite(psi, t) for psi in phi.subterms]
                if len(y_sub) != 2:
                    raise TransformationError(f"Non-binary builtin atom {phi} not supported")
                return get_pysmt_predicate(phi.predicate.symbol)(y_sub[0], y_sub[1])
            return self.smt_atom(phi, t)

        elif isinstance(phi, CompoundTerm):
            if phi.symbol.builtin:
                y_sub = [self.rewrite(psi, t) for psi in phi.subterms]
                if len(y_sub) != 2:
                    raise TransformationError("springroll.Theory", phi, "Only built-in binary functions are supported")
                return get_pysmt_predicate(phi.symbol.symbol)(y_sub[0], y_sub[1])
            # MRJ: all terms which are not builtin are supposed to be grounded and already
            # tracked by the theory
            try:
                params = []
                for st in phi.subterms:
                    try:
                        params.append(self.vars[(symref(st), t)])
                    except KeyError:
                        params.append(self.resolve_constant(st))
                fterm = self.create_function_application_term(phi.symbol, params, t)
                self.vars[symref(phi), t] = fterm
                return fterm
            except TermIsNotVariable:
                return self.resolve_constant(phi)
        elif isinstance(phi, Variable):
            return self.xt(phi, t)
        elif isinstance(phi, Constant):
            return self.resolve_constant(phi)
        elif isinstance(phi, float):
            return self.resolve_constant(phi)
        elif isinstance(phi, int):
            return self.resolve_constant(phi)
        else:
            raise TransformationError("springroll.Theory", phi,
                                      "Did not know how to translate formula of type '{}'!".format(type(phi)))

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

    def extract_plan(self):
        plan = OrderedDict()
        for idx, a in self.a.items():
            act_name, t = idx
            i = self.interpret_term(self.model, a)
            if i.constant_value():
                try:
                    plan[t] += [(act_name, 1)]
                except KeyError:
                    plan[t] = [(act_name, 1)]
        for idx, b in self.b.items():
            act_name, t = idx
            i = self.interpret_term(self.model, b)
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
        for idx, a in self.a.items():
            act_name, t = idx
            value = self.interpret_term(self.model, a)
            if value:
                print('{}@{}'.format(act_name, t))
        for idx, b in self.b.items():
            act_name, t = idx
            value = self.interpret_term(self.model, b)

            if value > 0:
                print('{}@{}={}'.format(act_name, t, value))
