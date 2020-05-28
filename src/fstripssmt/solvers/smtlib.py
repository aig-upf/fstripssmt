"""
    A mapping of Tarski-based theories into the CVC4 API, exploiting its support for set theory.
"""

import itertools
from collections import defaultdict
from datetime import datetime

from multipledispatch import dispatch


from tarski.syntax import symref, Sort, CompoundFormula, QuantifiedFormula, Tautology, CompoundTerm, Atom, \
    Contradiction, Function, Constant, Variable, Quantifier, BuiltinFunctionSymbol, BuiltinPredicateSymbol
from tarski.syntax.sorts import parent, Set, Interval
from tarski.syntax.util import get_symbols
from tarski.syntax.walker import FOLWalker

from fstripssmt.errors import TransformationError
from fstripssmt.solvers.common import SMTTranslator


# A mapping between Tarski set operators and their corresponding CVC4 name
# see https://cvc4.github.io/sets-and-relations
SET_SYMBOL_MAPPING = {
    BuiltinFunctionSymbol.SET_CARDINALITY: "card",
    BuiltinFunctionSymbol.SET_UNION: "union",
    BuiltinFunctionSymbol.SET_INTERSECTION: "intersection",
    BuiltinFunctionSymbol.SET_DIFFERENCE: "setminus",
    BuiltinPredicateSymbol.SET_IN: "member"
}


def translate_operator_name(symbol):
    if not symbol.builtin:
        return symbol.name

    name = SET_SYMBOL_MAPPING.get(symbol.name)
    if name is not None:
        return name

    # Otherwise assume we have a builtin arithmetic operator and return its string representation:
    if symbol.name == BuiltinPredicateSymbol.NE:
        # A bit of an exceptional case, for != we need to unwrap into (not (= ...))
        return None
    return str(symbol.name)


class SMTLibTheory:
    def __init__(self):
        self.declarations = []
        self.assertions = []

    def iterate_over_smtlib_declaration(self, comments=None, print_check_sat=False):
        if comments is not None:
            yield f';; File automatically generated on {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}'

        yield "(set-logic ALL_SUPPORTED)"

        if comments is not None:
            yield ""

        for x in self.declarations:
            yield x

        if comments is not None:
            yield ""

        # Comments are indexed wrt the assertions only
        for i, line in enumerate(self.assertions, start=0):
            if comments is not None and i in comments:
                yield f"\n{comments[i]}"
            yield line

        if comments is not None:
            yield ""

        # Check-sat command
        if print_check_sat:
            yield "(check-sat)"


class SMTLIBTranslator(SMTTranslator, FOLWalker):
    """ """

    def __init__(self, smtlang, static_symbols, action_names):
        SMTTranslator.__init__(self, smtlang, static_symbols, action_names)
        FOLWalker.__init__(self, raise_on_undefined=True)

    def simplify(self, x):
        # No simplification so far
        return x

    @dispatch(object)
    def visit(self, node):  # pylint: disable-msg=E0102
        return self.default_handler(node)

    def translate(self, theory):
        result = SMTLibTheory()

        # Functions and predicates
        for s in get_symbols(self.smtlang, type_="all", include_builtin=False):
            # arity=0 implies the symbol is not fluent, but static symbols of arity 0 should have
            # already been compiled away
            assert s.arity > 0
            dom = [resolve_type_for_sort(self.smtlang, sort) for sort in s.domain]
            codomain = resolve_type_for_sort(self.smtlang, s.codomain) if isinstance(s, Function) else "Bool"
            result.declarations.append(f'(declare-fun {s.name} ({" ".join(dom)}) {codomain})')

        # Theory translation
        ut = Untyper(self.smtlang, self.sort_bounds)
        for i, phi in enumerate(theory, start=1):
            phi_prime = ut.untype(phi)  # Compile away first possible typed quantifications
            rewritten = self.run(phi_prime, inplace=False)
            result.assertions.append(f"(assert {rewritten.smtlib})")

        return result

    @staticmethod
    def print_args(args):
        return ' '.join(x.smtlib for x in args)

    @dispatch(Tautology)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = "true"
        return node

    @dispatch(Contradiction)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = "false"
        return node

    @dispatch(CompoundTerm)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = self.visit_compound_expression(node)
        return node

    @dispatch(Atom)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = self.visit_compound_expression(node)
        return node

    def visit_compound_expression(self, node):
        opname = translate_operator_name(node.symbol)
        if opname is None:
            # A bit of an exceptional case, for != we need to unwrap into (not (= ...))
            return f"(not (= {self.print_args(node.subterms)}))"
        return f"({opname} {self.print_args(node.subterms)})"

    @dispatch(CompoundFormula)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = f'({node.connective} {self.print_args(node.subformulas)})'
        return node

    @dispatch(Variable)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = f'{node.symbol}'
        return node

    @dispatch(Constant)
    def visit(self, node):  # pylint: disable-msg=E0102
        node.smtlib = self.resolve_constant(node)
        return node

    @dispatch(QuantifiedFormula)
    def visit(self, node):  # pylint: disable-msg=E0102
        vlist = node.variable_declarations
        if node.quantifier == Quantifier.Exists:
            # Exist x . type(x) and \phi
            node.smtlib = f'(exists {vlist} (and {node.variable_bounds} {node.formula.smtlib}))'

        else:
            # Forall x . type(x) implies \phi
            node.smtlib = f'(forall {vlist} (=> {node.variable_bounds} {node.formula.smtlib}))'
        return node

    def resolve_constant(self, c: Constant, sort: Sort = None):
        if sort is None:
            sort = c.sort

        if sort in (self.smtlang.Integer, self.smtlang.Real):
            return str(sort.literal(c))

        if isinstance(sort, Interval):
            return self.resolve_constant(c, parent(sort))

        if isinstance(sort, Set):
            # This is slightly tricky, since set denotations are encoded with strings, not with Constant objects
            assert isinstance(c.symbol, set)
            elems = [self.resolve_constant(self.smtlang.get(x)) if isinstance(x, str) else str(x) for x in c.symbol]

            if len(c.symbol) == 0:
                return f"(as emptyset {resolve_type_for_sort(self.smtlang, c.sort)})"
            elif len(c.symbol) == 1:
                return f"(singleton {' '.join(elems)})"
            else:
                # e.g. if the set is {1, 2, 3, 4}, we want to output: (insert 1 2 3 (singleton 4))
                return f'(insert {" ".join(elems[:-1])} (singleton {elems[-1]}))'

        # Otherwise we must have an enumerated type and simply return the object ID
        return str(self.object_ids[symref(c)])

    def print_as_smtlib(self, smttheory, comments, cout):
        for line in smttheory.iterate_over_smtlib_declaration(comments, print_check_sat=True):
            print(line, file=cout)

    def extract_parallel_plan(self, solver, horizon, print_full_model):
        plan = defaultdict(list)

        for a in self.action_names:
            pred = self.smtlang.get(a)
            for binding in compute_signature_bindings(self.smtlang, pred.domain, horizon):
                term = pred(*binding)
                smtlib_term = self.run(term, inplace=False)
                if solver.get_value(smtlib_term.smtlib):
                    # Store the action without the time parameter
                    timestep = int(binding[-1].name)
                    plan[timestep] += [f'({a} {" ".join(str(elem.name) for elem in binding[:-1])})']

        # Useful for debugging
        # if print_full_model:
        #     # print("Model:", model)
        #     print("A list of all atoms: ")
        #     for pred in get_symbols(self.smtlang, type_="all", include_builtin=False):
        #         print(pred)
        #         for binding in compute_signature_bindings(self.smtlang, pred.domain, horizon+1):
        #             l0_term = pred(*binding)
        #             term = self.rewrite(l0_term, {}, horizon)
        #             print(f"{l0_term}: {model[term]}")
        #             # if model[term].constant_value():
        #             #     print(term)

        return plan


def linearize_parallel_plan(plan):
    timesteps = sorted(plan.keys())
    return list(itertools.chain.from_iterable(plan[t] for t in timesteps))


def compute_signature_bindings(lang, signature, horizon):
    domains = []
    for s in signature:
        domains.append(list(s.domain()))

    for binding in itertools.product(*domains):
        yield binding


class Untyper(FOLWalker):
    def __init__(self, smtlang, sort_bounds):
        super().__init__(raise_on_undefined=False)
        self.smtlang = smtlang
        self.sort_bounds = sort_bounds

    def untype(self, phi):
        """ Compile away the typed quantifiers by labeling all quantification nodes in the AST of the given formula
        with the quantification bounds that would correspond to an untyped quantification.
        The bounds are left as a string in attribute "variable_bounds" of the AST node.
        """
        x = self.run(phi, inplace=True)
        return x

    @dispatch(object)
    def visit(self, node):  # pylint: disable-msg=E0102
        return self.default_handler(node)

    @dispatch(QuantifiedFormula)
    def visit(self, node: QuantifiedFormula):  # pylint: disable-msg=E0102
        node.variable_bounds, node.variable_declarations = self.process_variables(node.variables)
        return node

    def process_variables(self, variables):
        conjuncts, declarations = [], []
        for v in variables:
            # The two unbound cases induce no bounds:
            if v.sort in (self.smtlang.Integer, self.smtlang.Real):
                continue

            # Otherwise assume we have a bounded type (including Enumerated types)
            lb, up = self.get_expression_bounds(v)
            if lb >= up:
                raise TransformationError(f"Variable corresponding to sort '{v.sort}' has cardinality 0")

            if up == lb+1:
                conjuncts += [f'(= {v.symbol} {lb})']
            else:
                conjuncts += [f'(>= {v.symbol} {lb})', f'(< {v.symbol} {up})']
            declarations += [f'({v.symbol} {resolve_type_for_sort(self.smtlang, v.sort)})']

        if not conjuncts:
            return "", ""

        return f"(and {' '.join(conjuncts)})", f"({' '.join(declarations)})"

    def get_expression_bounds(self, expr):
        s = expr.sort
        if s == s.language.Timestep:  # Timestep bounds are inclusive
            return s.lower_bound, s.upper_bound

        # Note that bounds in the other Tarski intervals are inclusive, while here we expect an exclusive upper bound
        return (s.lower_bound, s.upper_bound + 1) if isinstance(s, Interval) else self.sort_bounds[s]


def resolve_type_for_sort(lang, s):
    if s == lang.Integer:
        return "Int"

    if s == lang.Real:
        return "Real"

    if s is bool:
        return "Bool"

    if isinstance(s, Interval):
        return resolve_type_for_sort(lang, parent(s))

    if isinstance(s, Set):
        t = resolve_type_for_sort(lang, s.subtype)
        return f'(Set {t})'

    # Otherwise we have an enumerated type, which we'll model as an integer
    return "Int"
