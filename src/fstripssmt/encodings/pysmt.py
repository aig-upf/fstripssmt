from tarski.syntax import Connective
from tarski.syntax.builtins import BuiltinPredicateSymbol, BuiltinFunctionSymbol

from pysmt.shortcuts import LE, GE, Equals, NotEquals, LT, GT, Plus, Minus, Times, Div
from pysmt.shortcuts import And, Or, Not


_TARSKI_TO_PYSMT = {
    BuiltinPredicateSymbol.EQ: Equals,
    BuiltinPredicateSymbol.NE: NotEquals,
    BuiltinPredicateSymbol.LT: LT,
    BuiltinPredicateSymbol.LE: LE,
    BuiltinPredicateSymbol.GT: GT,
    BuiltinPredicateSymbol.GE: GE,
    BuiltinFunctionSymbol.ADD: Plus,
    BuiltinFunctionSymbol.SUB: Minus,
    BuiltinFunctionSymbol.MUL: Times,
    BuiltinFunctionSymbol.DIV: Div
}

_TARSKI_CONNECTIVE_TO_PYSMT = {
    Connective.Not: Not,
    Connective.And: And,
    Connective.Or: Or,
}


def get_pysmt_predicate(symbol):
    pred = _TARSKI_TO_PYSMT.get(symbol)
    if pred is None:
        raise RuntimeError(f'No PySMT predicate defined for Tarski symbol "{symbol}"')
    return pred


def get_pysmt_connective(symbol):
    conn = _TARSKI_CONNECTIVE_TO_PYSMT.get(symbol)
    if conn is None:
        raise RuntimeError(f'No PySMT predicate defined for Tarski symbol "{symbol}"')
    return conn
