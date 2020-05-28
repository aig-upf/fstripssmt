from os import path

from tarski.benchmarks.blocksworld import generate_fstrips_blocksworld_problem
from tarski.benchmarks.counters import generate_fstrips_counters_problem
from tarski.benchmarks import storytellers

from fstripssmt.runner import run_on_problem
from tests.plan.common import reader, collect_strips_benchmarks

here = path.abspath(path.dirname(__file__))
benchmarks = path.abspath(path.join(here, '..', '..', 'benchmarks'))


def test_on_storytellers():
    problem = storytellers.generate_problem(nstorytellers=3, naudiences=2, nstories=6, goal_type="equality")
    plan = run_on_problem(problem, reachability="none", max_horizon=2, grounding='none',
                          smtlib_filename="theory.smtlib", print_full_model=True, solver_name="cvc4")
    assert plan == ['(move b1 table)']


def test_on_storytellers_ground():
    problem = storytellers.generate_problem(nstorytellers=3, naudiences=2, nstories=6, goal_type="equality")
    plan = run_on_problem(problem, reachability="none", max_horizon=4, grounding='full',
                          smtlib_filename="theory.smtlib", print_full_model=True, solver_name="cvc4")
    assert plan == ['(move b1 table)']


def test_on_fstrips_bw():
    # Let's test the approach on one problem with non-numeric functions and a simple nested expression:
    #     move(x, y) action has an add-effect $clear(loc(x))$
    problem = generate_fstrips_blocksworld_problem(
        nblocks=2,
        init=[('b1', 'b2'), ('b2', 'table')],
        goal=[('b2', 'table'), ('b1', 'table')]
    )

    plan = run_on_problem(problem, reachability="none", max_horizon=1, grounding='none',
                          smtlib_filename="theory.smtlib", print_full_model=True)
    assert plan == ['(move b1 table)']

    problem = generate_fstrips_blocksworld_problem(
        nblocks=2,
        init=[('b1', 'b2'), ('b2', 'table')],
        goal=[('b2', 'b1'), ('b1', 'table')]
    )

    assert run_on_problem(problem, reachability="none", max_horizon=1, grounding='none') is None
    assert run_on_problem(problem, reachability="none", max_horizon=2, grounding='none') ==\
           ['(move b1 table)', '(move b2 b1)']

    problem = generate_fstrips_blocksworld_problem(
        nblocks=4,
        init=[('b1', 'b2'), ('b2', 'table'), ('b3', 'b4'), ('b4', 'table')],
        goal=[('b2', 'b3'), ('b3', 'b4'), ('b4', 'b1'), ('b1', 'table')]
    )

    # h=3 is not enough
    assert run_on_problem(problem, reachability="none", max_horizon=3, grounding='none') is None

    # h=4 is not enough
    assert run_on_problem(problem, reachability="none", max_horizon=4, grounding='none') is None

    # But there is a length-5 plan
    plan = run_on_problem(problem, reachability="none", max_horizon=5, grounding='none')
    possible_plans = ({'(move b1 table)', '(move b3 table)', '(move b4 b1)', '(move b3 b4)', '(move b2 b3)'},
                      {'(move b1 table)', '(move b3 b2)', '(move b4 b1)', '(move b3 b4)', '(move b2 b3)'},)
    assert plan is not None and set(plan) in possible_plans


def test_on_counters():
    counters = generate_fstrips_counters_problem(ncounters=3)
    # Optimal plan is a length-3 sequence with 'increment(c2)', 'increment(c3)', 'increment(c3)'
    assert run_on_problem(counters, reachability="none", max_horizon=1, grounding='none') is None,\
        "Not solvable in 1 timestep"
    assert run_on_problem(counters, reachability="none", max_horizon=2, grounding='none') is None, \
        "Not solvable in 2 timesteps"

    plan = run_on_problem(counters, reachability="none", max_horizon=3, grounding='none')
    assert len(plan) == 3 and plan.count('(increment c3)') == 2 and plan.count('(increment c2)') == 1


def test_on_blocks():
    instance_file, domain_file = collect_strips_benchmarks(["blocks:probBLOCKS-4-0.pddl"])[0]
    problem = reader().read_problem(domain_file, instance_file)
    # The only optimal plan has length 6
    assert run_on_problem(problem, reachability="none", max_horizon=5, grounding='none') is None
    plan = run_on_problem(problem, reachability="none", max_horizon=6, grounding='none')
    assert plan == ['(pick-up b)', '(stack b a)', '(pick-up c)', '(stack c b)', '(pick-up d)', '(stack d c)']


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
