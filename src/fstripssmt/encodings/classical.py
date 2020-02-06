import itertools
from collections import OrderedDict

import tarski.fstrips as fs
from tarski import Constant, Term, Variable, Function
from tarski.syntax import symref, Sort, Connective, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    neg

import pysmt
from pysmt.shortcuts import FreshSymbol, Symbol
from pysmt.shortcuts import Bool, Int, Real, FunctionType
from pysmt.shortcuts import LE, GE, Equals, NotEquals, LT, GT
from pysmt.shortcuts import And, Implies, Or, TRUE, FALSE, Not, ToReal
from pysmt.typing import INT, BOOL, REAL
from pysmt.shortcuts import Solver

from fstripssmt.encodings.pysmt import get_pysmt_predicate
from fstripssmt.errors import TransformationError


class ClassicalEncoding(object):
    """ """

    def __init__(self, problem: fs.Problem):
        self.problem = problem
        self.language = self.problem.language

        self.interference = OrderedDict()
        self.determine_interference()

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
        theory += self.assert_initial_state_axiom()
        return theory

    def determine_interference(self):
        self.interference = OrderedDict()
        for act_name, act in self.problem.actions.items():

            for eff in act.effects:
                if isinstance(eff, fs.DelEffect):
                    try:
                        self.interference[symref(eff.atom)] += [act]
                    except KeyError:
                        self.interference[symref(eff.atom)] = [act]
                if isinstance(eff, fs.AddEffect):
                    try:
                        self.interference[symref(eff.atom)] += [act]
                    except KeyError:
                        self.interference[symref(eff.atom)] = [act]
                elif isinstance(eff, fs.LiteralEffect):
                    if isinstance(eff.lit, CompoundFormula) and eff.lit.connective == Connective.Not:
                        try:
                            self.interference[symref(eff.lit.subformulas[0])] += [act]
                        except KeyError:
                            self.interference[symref(eff.atom)] = [act]
                elif isinstance(eff, fs.FunctionalEffect):
                    try:
                        self.interference[symref(eff.lhs)] += [act]
                    except KeyError:
                        self.interference[symref(eff.lhs)] = [act]
                elif isinstance(eff, fs.LinearEffect):
                    for y in eff.y[:, 0]:
                        try:
                            self.interference[symref(y)] += [act]
                        except KeyError:
                            self.interference[symref(y)] = [act]

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

    def create_bool_term(self):
        return FreshSymbol(BOOL)

    def create_int_term(self):
        return FreshSymbol(INT)

    def create_variable(self, var):
        if var.sort == self.language.Integer:
            y_var = FreshSymbol(INT)
        elif var.sort == self.language.Real:
            y_var = FreshSymbol(REAL)
        else:
            y_var = FreshSymbol(INT)
            self.create_domain_axioms(y_var, var.sort)
        return y_var

    def SAT(self):
        self.model = None
        # assert
        self.status = False
        with Solver() as solver:
            for axiom_set in self.axioms:
                for phi in axiom_set:
                    solver.add_assertion(phi)
            self.status = solver.solve()

            if self.status:
                self.model = solver.get_model()

        return self.status

    def xt(self, term, timepoint):
        try:
            xt = self.vars[symref(term), timepoint]
        except KeyError:
            xt = self.create_variable(term)
            self.vars[symref(term), timepoint] = xt
        return xt

    def pt(self, pred, timepoint):
        try:
            pt = self.vars[symref(pred), timepoint]
        except KeyError:
            pt = self.create_boolean(pred)
            self.vars[symref(pred), timepoint] = pt
        return pt

    def at(self, action, timepoint):
        try:
            at = self.a[action.ident(), timepoint]
        except KeyError:
            at = self.create_bool_term()
            self.a[action.ident(), timepoint] = at
        return at

    def bt(self, action, timepoint):
        try:
            bt = self.b[action.ident(), timepoint]
        except KeyError:
            bt = self.create_int_term()
            self.b[action.ident(), timepoint] = bt
        return bt

    def assert_initial_state_axiom(self):
        for idx, sv in self.state_variables.enumerate():
            x = sv.symbol(*sv.binding)
            if isinstance(x, Atom):
                if self.problem.init[x]:
                    self.Init += [self.pt(x, 0)]
                else:
                    self.Init += [Not(self.pt(x, 0))]
            elif isinstance(x, CompoundTerm):
                self.Init += [self.rewrite(x == self.problem.init[x], 0)]

    def assert_goal_axiom(self, n):
        self.Goal += [self.rewrite(self.problem.goal, n)]

    def assert_propositional_action_axioms(self, a, t):
        self.ActionPreconditions += [Implies(self.at(a, t), self.rewrite(a.precondition, t))]
        for eff in a.effects:
            if isinstance(eff, fs.AddEffect):
                self.ActionEffects += [Implies(self.at(a, t), self.rewrite(eff.atom, t + 1))]
            elif isinstance(eff, fs.DelEffect):
                self.ActionEffects += [Implies(self.at(a, t), self.rewrite(neg(eff.atom), t + 1))]
            elif isinstance(eff, fs.LiteralEffect):
                self.ActionEffects += [Implies(self.at(a, t), self.rewrite(eff.lit, t + 1))]
            elif isinstance(eff, fs.FunctionalEffect):
                lhs = self.rewrite(eff.lhs, t + 1)
                rhs = self.rewrite(eff.rhs, t)
                self.ActionEffects += [Implies(self.at(a, t), Equals(lhs, rhs))]
            else:
                raise TransformationError("Springroll: can't compile effect: {}".format(eff))

    def assert_frame_axioms(self, t):
        for symbol_ref, A in self.interference.items():
            if isinstance(symbol_ref.expr, Atom):
                x_i = self.pt(symbol_ref.expr, t)
                x_i1 = self.pt(symbol_ref.expr, t + 1)
            elif isinstance(symbol_ref.expr, CompoundTerm):
                x_i = self.xt(symbol_ref.expr, t)
                x_i1 = self.xt(symbol_ref.expr, t + 1)
            a_terms = []
            for act in A:
                try:
                    a = self.a[act.ident(), t]
                    a_terms += [a]
                except KeyError:
                    b = self.b[act.ident(), t]
                    a_terms += [GT(b, Int(0))]
            self.Persistence += [Implies(NotEquals(x_i, x_i1), Or(a_terms))]

    def assert_interference_axioms(self, t):
        for symbol_ref, A in self.interference.items():
            if len(A) < 2: continue
            for a1, a2 in itertools.combinations(A, 2):
                terms = []
                try:
                    a = self.a[a1.ident(), t]
                    terms += [a]
                except KeyError:
                    a = self.b[a1.ident(), t]
                    terms += [Equals(a, Int(0))]
                try:
                    a = self.a[a2.ident(), t]
                    terms += [a]
                except KeyError:
                    a = self.b[a2.ident(), t]
                    terms += [Equals(a, Int(0))]
                self.Interference += [Or(terms)]

    def rewrite(self, phi, t):
        if isinstance(phi, QuantifiedFormula):
            raise TransformationError("springroll.Theory:(): formula {} is not quantifier free!".format(phi))
        elif isinstance(phi, Tautology):
            return TRUE()
        elif isinstance(phi, CompoundFormula):
            y_sub = [self.rewrite(psi, t) for psi in phi.subformulas]
            if phi.connective == Connective.Not:
                return Not(y_sub[0])
            elif phi.connective == Connective.And:
                return And(y_sub[0], y_sub[1])
            elif phi.connective == Connective.Or:
                return Or(y_sub[0], y_sub[1])
        elif isinstance(phi, Atom):
            if phi.predicate.builtin:
                y_sub = [self.rewrite(psi, t) for psi in phi.subterms]
                if len(y_sub) != 2:
                    raise TransformationError("springroll.Theory:", phi,
                                              "Only built-in binary predicates are supported")
                return get_pysmt_predicate(phi.predicate.symbol)(y_sub[0], y_sub[1])
            return self.pt(phi, t)
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
