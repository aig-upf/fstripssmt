import copy

from multipledispatch import dispatch
from tarski import Function, Predicate, Term, Variable
from tarski.fstrips import AddEffect, SingleEffect, FunctionalEffect, DelEffect
from tarski.fstrips.walker import ProblemWalker, WalkerContext
from tarski.grounding.ops import approximate_symbol_fluency
from tarski.syntax import Atom, Constant, CompoundTerm
from tarski.theories import load_theory


class NestedExpressionWalker(ProblemWalker):
    def __init__(self, problem):
        super().__init__()
        self.problem = problem
        _, self.static_symbols = approximate_symbol_fluency(problem)
        self.nested_symbols = dict()

    def get_replacement(self, symbol):
        try:
            return self.nested_symbols[symbol]
        except KeyError:
            res = self.nested_symbols[symbol] = self.create_replacement(symbol)
            return res

    @staticmethod
    def create_replacement(symbol):
        assert isinstance(symbol, Predicate)
        lang = symbol.language
        sname = symbol.name

        # TODO: (Not urgent) Remove predicate from language? Better later once the substitution is done
        load_theory(lang, "boolean")
        return lang.function(f"_f{sname}", *symbol.sort, lang.Boolean)

    def _visit_compound(self, node):
        if all(isinstance(s, (Constant, Variable)) for s in node.subterms):
            return node  # No nestedness

        symbol = node.symbol
        lang = symbol.language

        if symbol.builtin:
            return node

        if symbol in self.static_symbols:
            raise RuntimeError("Unimplemented")

        # We have a fluent symbol, replace the expression with a new symbol when appropriate
        if isinstance(symbol, Function):
            # Simply mark the symbol as nested, but return the same node, we don't want to replace functions
            self.nested_symbols[symbol] = None
            return node

        term = self.get_replacement(node.symbol)(*node.subterms)

        if self.context == WalkerContext.Effect:
            return term
        return term == lang.get("True")

    def visit_effect(self, effect, inplace=True):
        effect = effect if inplace else copy.deepcopy(effect)

        assert isinstance(effect, SingleEffect)
        effect.condition = self.visit_expression(effect.condition)

        if isinstance(effect, (AddEffect, DelEffect)):
            effect.atom = self.visit_effect_atom(effect.atom)
            if isinstance(effect.atom, Term):
                # Transform the predicative effect into a functional effect
                val = effect.atom.language.get("True" if isinstance(effect, AddEffect) else "False")
                effect = effect.atom << val

        elif isinstance(effect, FunctionalEffect):
            effect.lhs = self.visit_effect_atom(effect.lhs)
            effect.rhs = self.visit_effect_atom(effect.rhs)

        else:
            raise RuntimeError(f'Effect "{effect}" of type "{type(effect)}" cannot be analysed')

        return self.visit(effect)

    @dispatch(object)
    def visit(self, node):
        return self.default_handler(node)

    @dispatch(Atom)
    def visit(self, node):
        return self._visit_compound(node)

    @dispatch(CompoundTerm)
    def visit(self, node):
        return self._visit_compound(node)


def compile_nested_predicates_into_functions(problem):
    walker = NestedExpressionWalker(problem)
    problem = walker.run(problem, inplace=True)
    return problem, walker.nested_symbols
