# A mapping of Tarski-based theories into PySMT.
import itertools
from collections import defaultdict
from datetime import datetime

import pysmt
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript, smtlibscript_from_formula, SmtLibCommand

from tarski.syntax import symref, Sort, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Interval, Contradiction, term_substitution, forall, land, implies, lor, exists, Function, Constant, Variable, \
    Quantifier
from pysmt.shortcuts import FreshSymbol, Symbol, EqualsOrIff, Int, Real, FunctionType, And, ForAll, Exists, get_env
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

    def __init__(self, smtlang, static_symbols, action_names):
        assert has_theory(smtlang, "arithmetic")
        self.smtlang = smtlang
        self.static_symbols = static_symbols
        self.action_names = action_names

        # Compute a sort-contiguous object ID assignment
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.smtlang)
        # print(self.sort_bounds)
        # print(self.object_ids)

        self.vars = dict()
        self.theory = []

        self.smt_functions, self.actionvars = self.setup_language(smtlang)

    def setup_language(self, smtlang):
        smt_funs = dict()
        smt_actions = dict()
        for s in get_symbols(smtlang, type_="all", include_builtin=False):
            # arity=0 implies the symbol is not fluent, but static symbols of arity 0 should have
            # already been compiled away
            assert s.arity > 0
            fun, ftype = self.create_function_type(s)
            smt_funs[s.name] = (fun, ftype)

            if s.name in self.action_names:
                smt_actions[s.name] = (s, fun)
        return smt_funs, smt_actions

    def create_function_type(self, fun: Function):
        domain_types = [self.resolve_type_for_sort(s) for s in fun.domain]
        codomain_type = self.resolve_type_for_sort(fun.codomain) if isinstance(fun, Function) else BOOL
        funtype = FunctionType(codomain_type, domain_types)
        return Symbol(fun.name, funtype), funtype

    def translate(self, theory, horizon):
        # TODO the `horizon` shouldn't be necessary here, but so far we cannot have a bounded *natural* interval in
        #      Tarski, so we have this ugly workaround. Should fix this in Tarski and clean this up
        for i, phi in enumerate(theory, start=1):
            # print(f'Translating SMT sentence #{i}')
            if not isinstance(phi, str):
                self.theory.append(self.rewrite(phi, {}, horizon))
        return self.theory

    def rewrite(self, phi, varmap, horizon):

        if isinstance(phi, QuantifiedFormula):
            return self.rewrite_quantified_formula(phi, varmap, horizon)

        elif isinstance(phi, Tautology):
            return TRUE()

        elif isinstance(phi, Contradiction):
            return FALSE()

        elif isinstance(phi, CompoundFormula):
            pysmt_fun = get_pysmt_connective(phi.connective)
            return pysmt_fun(*(self.rewrite(psi, varmap, horizon) for psi in phi.subformulas))

        elif isinstance(phi, (Atom, CompoundTerm)):
            if phi.symbol.builtin:
                if len(phi.subterms) != 2:
                    raise TransformationError(f"Unsupported non-binary builtin expression {phi}")
                lhs, rhs = (self.rewrite(psi, varmap, horizon) for psi in phi.subterms)
                return get_pysmt_predicate(phi.symbol.symbol)(lhs, rhs)

            return self.smt_fun_application(phi, varmap, horizon)
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

    def rewrite_quantified_formula(self, phi, varmap, horizon):
        vars_, bounds = zip(*(self.create_quantified_variable(v, horizon) for v in phi.variables))
        # We merge the two variable assignments:
        varmap.update((v.symbol, pysmt_var) for v, pysmt_var in zip(phi.variables, vars_))
        if phi.quantifier == Quantifier.Exists:
            creator = Exists
            # Exist x . type(x) and \phi
            f = And(And(*bounds), self.rewrite(phi.formula, varmap, horizon))

        else:
            # Forall x . type(x) implies \phi
            creator = ForAll
            f = Implies(And(*bounds), self.rewrite(phi.formula, varmap, horizon))

        return creator(vars_, f)

    def smt_fun_application(self, phi, varmap, horizon):
        key = symref(phi)
        try:
            return self.vars[key]
        except KeyError:
            params = [self.rewrite(st, varmap, horizon) for st in phi.subterms]
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

    def create_quantified_variable(self, v, horizon):
        if v.sort == self.smtlang.Integer:
            return Symbol(v.symbol, INT), TRUE()

        if v.sort == self.smtlang.Real:
            # This is a HACK: currently the only real-typed entities we can have are timestep, which unfortunately with
            # the current Tarski architecture is not easy to specify as naturals. The current solution is to remap them
            # back to ints here, AND to force the timestep bounds given by the theory horizon
            # return Symbol(v.symbol, REAL), TRUE()
            smtvar = Symbol(v.symbol, INT)
            lb, up = 0, horizon
            return smtvar, And(GE(smtvar, Int(lb)), LT(smtvar, Int(up)))

        # if isinstance(v.sort, Interval):
        #     # TODO This won't work for real intervals, of course.
        #     return Symbol(v.symbol, INT)

        # Otherwise assume we have a enumerated type and simply return the index of the object
        smtvar = Symbol(v.symbol, INT)

        lb, up = self.get_expression_bounds(v)
        if lb >= up:
            raise TransformationError(f"SMT variable corresponding to sort '{v.sort}' has cardinality 0")

        bounds = And(GE(smtvar, Int(lb)), LT(smtvar, Int(up)))
        return smtvar, bounds

    def get_expression_bounds(self, expr):
        s = expr.sort
        # Note that bounds in Tarski intervals are inclusive, while here we expect an exclusive upper bound
        return (s.lower_bound, s.upper_bound+1) if isinstance(s, Interval) else self.sort_bounds[s]

    def extract_parallel_plan(self, model, horizon):
        plan = defaultdict(list)

        for aname, (pred, smt_node) in self.actionvars.items():
            for binding in self.compute_signature_bindings(pred.domain, horizon):
                term = self.rewrite(pred(*binding), {}, horizon)
                if model[term].constant_value():
                    timestep = int(binding[-1].name)
                    args = ", ".join(elem.name for elem in binding[:-1])
                    plan[timestep] += [f"{aname}({args})"]

        # A bit of debugging
        print("A list of all atoms: ")
        for pred in get_symbols(self.smtlang, type_="all", include_builtin=False):
            print(pred)
            for binding in self.compute_signature_bindings(pred.domain, horizon+1):
                l0_term = pred(*binding)
                term = self.rewrite(l0_term, {}, horizon)
                print(f"{l0_term}: {model[term]}")
                # if model[term].constant_value():
                #     print(term)

        return plan

    def compute_signature_bindings(self, signature, horizon):
        domains = []
        for s in signature:
            if s != self.smtlang.Real:
                assert not s.builtin  # Better don't generate the domain of a builtin type :-)
                domains.append(list(s.domain()))
            else:
                domains.append(list(Constant(x, self.smtlang.Real) for x in range(0, horizon)))

        for binding in itertools.product(*domains):
            yield binding

    # **************** SOME OLD CODE THAT COULD STILL BE USEFUL FOLLOWS **************** #
    # **************** SOME OLD CODE THAT COULD STILL BE USEFUL FOLLOWS **************** #

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

    def decode_model(self, model):
        for (sref, t), x in self.vars.items():
            print(f'{sref.expr}@{t} = {self.interpret_term(model, x)}')

        for (aname, t), a in self.actionvars.items():
            val = self.interpret_term(model, a)
            if val.constant_value():
                print('{}@{}'.format(aname, t))

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


def bool_to_pysmt_boolean(value):
    assert isinstance(value, bool)
    return TRUE() if value else FALSE()


def linearize_parallel_plan(plan):
    timesteps = sorted(plan.keys())
    return list(itertools.chain.from_iterable(plan[t] for t in timesteps))


def print_script_command_line(cout, name, args):
    script = SmtLibScript()
    script.add_command(SmtLibCommand(name=name, args=args))
    script.serialize(cout, daggify=False)


def print_as_smtlib(smt_formulas, comments, cout):
    # script = smtlibscript_from_formula(And(smt_formulas), logic="QF_UFIDL")
    # script = SmtLibScript()
    # script.add(name=smtcmd.SET_LOGIC, args=["QF_UFIDL"])
    print(f";; File automatically generated on {datetime.now()}", file=cout)

    print_script_command_line(cout, name=smtcmd.SET_LOGIC, args=["QF_UFIDL"])
    print("", file=cout)

    # The code below has largely been copied from smtlibscript_from_formula, with a few modifications
    # to work on a list of formulas
    # We simply create an And in order to be able to gather all types and free variables efficiently
    formula_and = And(smt_formulas)
    # Declare all types
    for type_ in get_env().typeso.get_types(formula_and, custom_only=True):
        # script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])
        print_script_command_line(cout, name=smtcmd.DECLARE_SORT, args=[type_.decl])
    print("", file=cout)

    # Declare all variables
    for symbol in formula_and.get_free_variables():
        assert symbol.is_symbol()
        # script.add(name=smtcmd.DECLARE_FUN, args=[symbol])
        print_script_command_line(cout, name=smtcmd.DECLARE_FUN, args=[symbol])

    print("", file=cout)

    # Assert formulas
    for i, formula in enumerate(smt_formulas, start=0):
        if i in comments:
            print(f"\n{comments[i]}", file=cout)
        # script.add_command(SmtLibCommand(name=smtcmd.ASSERT, args=[formula]))
        print_script_command_line(cout, name=smtcmd.ASSERT, args=[formula])

    print("\n", file=cout)

    # check-sat
    # script.add_command(SmtLibCommand(name=smtcmd.CHECK_SAT, args=[]))
    print_script_command_line(cout, name=smtcmd.CHECK_SAT, args=[])

    # script.serialize(cout, daggify=False)
