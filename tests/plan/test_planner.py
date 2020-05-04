from os import path

from tarski.benchmarks.blocksworld import generate_fstrips_blocksworld_problem
from tarski.benchmarks.counters import generate_fstrips_counters_problem
from tarski.fstrips.manipulation import Simplify
from tarski.syntax import land
from tarski.syntax.transform import compile_universal_effects_away

from fstripssmt.nested import compile_nested_predicates_into_functions, NestedExpressionWalker
from fstripssmt.runner import run_on_problem
from tests.plan.common import reader, collect_strips_benchmarks

here = path.abspath(path.dirname(__file__))
benchmarks = path.abspath(path.join(here, '..', '..', 'benchmarks'))


def test_on_fstrips_bw():
    # Let's test the approach on one problem with non-numeric functions and a simple nested expression:
    #     move(x, y) action has an add-effect $clear(loc(x))$
    problem = generate_fstrips_blocksworld_problem(
        nblocks=2,
        init=[('b1', 'b2'), ('b2', 'table')],
        goal=[('b2', 'table'), ('b1', 'table')]
    )

    plan = run_on_problem(problem, reachability="none", max_horizon=1)
    assert plan == ['move(b1, table)']

    problem = generate_fstrips_blocksworld_problem(
        nblocks=2,
        init=[('b1', 'b2'), ('b2', 'table')],
        goal=[('b2', 'b1'), ('b1', 'table')]
    )

    assert run_on_problem(problem, reachability="none", max_horizon=1) is None
    assert run_on_problem(problem, reachability="none", max_horizon=2) == ['move(b1, table)', 'move(b2, b1)']

    problem = generate_fstrips_blocksworld_problem(
        nblocks=4,
        init=[('b1', 'b2'), ('b2', 'table'), ('b3', 'b4'), ('b4', 'table')],
        goal=[('b2', 'b3'), ('b3', 'b4'), ('b4', 'b1'), ('b1', 'table')]
    )

    # h=3 is not enough
    assert run_on_problem(problem, reachability="none", max_horizon=3) is None

    # h=4 is not enough
    assert run_on_problem(problem, reachability="none", max_horizon=4) is None

    # But there is a length-5 plan
    plan = run_on_problem(problem, reachability="none", max_horizon=5)
    possible_plans = ({'move(b3, table)', 'move(b1, table)', 'move(b4, b1)', 'move(b3, b4)', 'move(b2, b3)'},
                      {'move(b1, table)', 'move(b2, b3)', 'move(b3, b2)', 'move(b3, b4)', 'move(b4, b1)'})
    assert plan is not None and set(plan) in possible_plans

# def test_on_counters():
#     counters = generate_fstrips_counters_problem(ncounters=3)
#     plan = run_on_problem(counters, reachability="none", max_horizon=4)
#     assert plan
#
#
# def test_on_blocks():
#     instance_file, domain_file = collect_strips_benchmarks(["blocks:probBLOCKS-4-0.pddl"])[0]
#     problem = reader().read_problem(domain_file, instance_file)
#
#     plan = run_on_problem(problem, reachability="full", max_horizon=6)
#     assert plan
#
#     plan = run_on_problem(problem, reachability="full", max_horizon=5)
#     assert plan is None  # Optimal plan has length 6
#
#
# def test_nested_expression_walker():
#     problem = generate_fstrips_blocksworld_problem()
#     lang = problem.language
#     b1, b2, clear, loc, table = lang.get('b1', 'b2', 'clear', 'loc', 'table')
#
#     walker = NestedExpressionWalker(problem)
#
#     node = walker.visit_expression((loc(b1) == table))
#     assert str(node) == '=(loc(b1),table)' and not walker.nested_symbols  # Nothing is changed
#
#     node = walker.visit_expression(land(clear(b1) & clear(loc(b1)) & clear(loc(b2)), flat=True))
#     assert str(node) == '((clear(b1) and =(_fclear(loc(b1)),True)) and =(_fclear(loc(b2)),True))'
#
#
# def test_nested_expression_compiler():
#     problem, _ = compile_nested_predicates_into_functions(generate_fstrips_blocksworld_problem(
#         nblocks=2,
#         init=[('b1', 'b2'), ('b2', 'table')],
#         goal=[('b2', 'table'), ('b1', 'table')]
#     ))
#     move = problem.get_action("move")
#     assert str(move.effects[1]) == '(T -> _fclear(loc(x)) := True)'
#     assert str(move.effects[2]) == '(T -> _fclear(y) := False)'
