# A mapping of Tarski-based theories into PySMT.
import itertools
from collections import defaultdict

import pysmt
from tarski.syntax import symref, Sort, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Interval, Contradiction, term_substitution, forall, land, implies, lor, exists, Function, Constant, Variable, \
    Quantifier
from pysmt.shortcuts import FreshSymbol, Symbol, EqualsOrIff, Int, Real, FunctionType, And, ForAll, Exists
from pysmt.shortcuts import LT, GE, Equals, Implies, Or, TRUE, FALSE, Not
from pysmt.typing import INT, BOOL, REAL
from tarski.syntax.sorts import parent
from tarski.syntax.util import get_symbols
from tarski.theories import has_theory
from tarski.syntax.ops import compute_sort_id_assignment

from fstripssmt.encodings.pysmt import get_pysmt_connective, get_pysmt_predicate
from fstripssmt.errors import TransformationError


class PySMTTranslator:
    """ """

    def __init__(self, smtlang, operators=None, statevars=None):
        assert has_theory(smtlang, "arithmetic")
        self.smtlang = smtlang
        self.operators = operators
        self.statevars = statevars

        # Compute a sort-contiguous object ID assignment
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.smtlang)
        # print(self.sort_bounds)
        # print(self.object_ids)

        self.vars = dict()

        # The boolean vars denoting application of an operator at a given timepoint
        self.actionvars = dict()
        self.smt_functions = dict()

        self.custom_domain_terms = dict()
        self.theory = []

        self.setup_language(smtlang)

    def setup_language(self, smtlang):
        for s in get_symbols(smtlang, type_="all", include_builtin=False):
            fun, ftype = self.create_function_type(s)
            self.smt_functions[s.name] = (fun, ftype)

    def create_function_type(self, fun: Function):
        assert fun.arity > 0  # Otherwise this would be a state variable
        domain_types = [self.resolve_type_for_sort(s) for s in fun.domain]
        codomain_type = self.resolve_type_for_sort(fun.codomain) if isinstance(fun, Function) else BOOL
        funtype = FunctionType(codomain_type, domain_types)
        return Symbol(fun.name, funtype), funtype

    def translate(self, theory):
        for i, phi in enumerate(theory, start=1):
            # print(f'Translating SMT sentence #{i}')
            if not isinstance(phi, str):
                self.theory.append(self.rewrite(phi, {}))
        return self.theory

    def rewrite(self, phi, varmap):

        if isinstance(phi, QuantifiedFormula):
            return self.rewrite_quantified_formula(phi, varmap)

        elif isinstance(phi, Tautology):
            return TRUE()

        elif isinstance(phi, Contradiction):
            return FALSE()

        elif isinstance(phi, CompoundFormula):
            pysmt_fun = get_pysmt_connective(phi.connective)
            return pysmt_fun(*(self.rewrite(psi, varmap) for psi in phi.subformulas))

        elif isinstance(phi, (Atom, CompoundTerm)):
            if phi.symbol.builtin:
                if len(phi.subterms) != 2:
                    raise TransformationError(f"Unsupported non-binary builtin expression {phi}")
                lhs, rhs = (self.rewrite(psi, varmap) for psi in phi.subterms)
                return get_pysmt_predicate(phi.symbol.symbol)(lhs, rhs)

            return self.smt_fun_application(phi, varmap)
            # if phi.symbol in self.nested_symbols:
            #     # Even if phi is a state variable, if its head symbol appears nested elsewhere, we'll need to deal
            #     # with it as an uninterpreted function
            #     return self.smt_fun_application(phi, t, subt)
            #
            # elif self.is_state_variable(phi):
            #     # For a state variable, simply return the (possibly cached) variable corresponding to it
            #     return self.smt_variable(phi, t)
            #
            # return self.smt_fun_application(phi, t, subt)

        elif isinstance(phi, Variable):
            if phi.symbol not in varmap:
                raise TransformationError(f'Free variable "{phi}" not allowed in transformation to SMT')
            return varmap[phi.symbol]

        elif isinstance(phi, Constant):
            return self.resolve_constant(phi)

        raise TransformationError(f"Don't know how to translate formula '{phi}'")

    def rewrite_quantified_formula(self, phi, varmap):
        vars_, bounds = zip(*(self.create_quantified_variable(v) for v in phi.variables))
        # We merge the two variable assignments:
        varmap.update((v.symbol, pysmt_var) for v, pysmt_var in zip(phi.variables, vars_))
        if phi.quantifier == Quantifier.Exists:
            creator = Exists
            # Exist x . type(x) and \phi
            f = And(And(*bounds), self.rewrite(phi.formula, varmap=varmap))

        else:
            # Forall x . type(x) implies \phi
            creator = ForAll
            f = Implies(And(*bounds), self.rewrite(phi.formula, varmap=varmap))

        return creator(vars_, f)

    def smt_fun_application(self, phi, varmap):
        key = symref(phi)
        try:
            return self.vars[key]
        except KeyError:
            params = [self.rewrite(st, varmap) for st in phi.subterms]
            fun, ftype = self.smt_functions[phi.symbol.name]
            self.vars[key] = res = pysmt.shortcuts.Function(fun, params)
        return res

    def resolve_type_for_sort(self, s):
        if s == self.smtlang.Integer:
            return INT
        elif s == self.smtlang.Real:
            # This is a HACK: currently the only real-typed entities we can have are timestep, which unfortunately with
            # the current Tarski architecture is not easy to specify as naturals. The current solution is to remap them
            # back to ints here
            # return REAL
            return INT
        elif s is bool:
            return BOOL
        else:  # We'll model enumerated types as integers
            return INT

    def resolve_constant(self, c: Constant, sort: Sort = None):
        if sort is None:
            sort = c.sort

        if sort == self.smtlang.Integer:
            return Int(c.symbol)

        if sort == self.smtlang.Real:
            # This is a HACK: currently the only real-typed entities we can have are timestep, which unfortunately with
            # the current Tarski architecture is not easy to specify as naturals. The current solution is to remap them
            # back to ints here
            # return Real(c.symbol)
            assert isinstance(c.symbol, int) or c.symbol.is_integer()
            return Int(int(c.symbol))

        if isinstance(sort, Interval):
            return self.resolve_constant(c, parent(sort))

        # Otherwise we must have an enumerated type and simply return the object ID
        return Int(self.object_ids[symref(c)])

    def create_quantified_variable(self, v):
        if v.sort == self.smtlang.Integer:
            return Symbol(v.symbol, INT), TRUE()

        if v.sort == self.smtlang.Real:
            # This is a HACK: currently the only real-typed entities we can have are timestep, which unfortunately with
            # the current Tarski architecture is not easy to specify as naturals. The current solution is to remap them
            # back to ints here
            # return Symbol(v.symbol, REAL), TRUE()
            return Symbol(v.symbol, INT), TRUE()

        # if isinstance(v.sort, Interval):
        #     # TODO This won't work for real intervals, of course.
        #     return Symbol(v.symbol, INT)

        # Otherwise assume we have a enumerated type and simply return the index of the object
        smtvar = Symbol(v.symbol, INT)

        lb, up = self.sort_bounds[v.sort]
        if lb >= up:
            raise TransformationError(f"SMT variable corresponding to sort '{v.sort}' has cardinality 0")

        bounds = And(GE(smtvar, Int(lb)), LT(smtvar, Int(up)))
        return smtvar, bounds

    def smt_variable(self, expr):
        # TODO This code is currently unused and needs to be revised / removed
        """ Return the (possibly cached) SMT theory variable that corresponds to the given Tarski
        logical expression, which can be either an atom (e.g. clear(b1)) or a compound term representing
        a state variable (e.g. value(c1)). """
        assert isinstance(expr, (Atom, CompoundTerm, Variable))
        key = symref(expr)
        try:
            return self.vars[key]
        except KeyError:
            creator = self.create_bool_term if isinstance(expr, Atom) else self.create_variable
            self.vars[key] = res = creator(expr, name=str(expr))
        return res

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

    # **************** SOME OLD CODE THAT COULD STILL BE USEFUL FOLLOWS **************** #
    # **************** SOME OLD CODE THAT COULD STILL BE USEFUL FOLLOWS **************** #

    def create_variable(self, elem, sort=None, name=None):
        # TODO This code is currently unused and needs to be revised / removed
        assert 0
        sort = elem.sort if sort is None else sort
        name = str(elem) if name is None else name

        if sort == self.smtlang.Integer:
            return Symbol(name, INT)

        if sort == self.smtlang.Real:
            return Symbol(name, REAL)

        if isinstance(sort, Interval):
            # Let's go seek the underlying type of the interval recursively!
            return self.create_variable(elem, parent(sort), name)

        # Otherwise assume we have a enumerated type and simply return the index of the object
        y_var = Symbol(name, INT)
        self.create_enum_type_domain_axioms(y_var, elem.sort)
        return y_var

    def create_enum_type_domain_axioms(self, y, sort):
        # TODO This code is currently unused and needs to be revised / removed
        assert 0
        self.custom_domain_terms[y] = sort
        lb, up = self.sort_bounds[sort]
        if lb >= up:
            raise TransformationError(f"SMT variable corresponding to sort '{sort}' has cardinality 0")

        self.theory += [GE(y, Int(lb)), LT(y, Int(up))]

    def smt_action(self, action, timepoint):
        # TODO This code is currently unused and needs to be revised / removed
        key = (action.ident(), timepoint)
        try:
            return self.actionvars[key]
        except KeyError:
            self.actionvars[key] = res = self.create_bool_term(action, name=f'{action.ident()}@{timepoint}')
        return res

    @staticmethod
    def create_bool_term(atom, name):
        # TODO This code is currently unused and needs to be revised / removed
        return Symbol(name, BOOL)


def bool_to_pysmt_boolean(value):
    assert isinstance(value, bool)
    return TRUE() if value else FALSE()


def linearize_parallel_plan(plan):
    timesteps = sorted(plan.keys())
    return list(itertools.chain.from_iterable(plan[t] for t in timesteps))

