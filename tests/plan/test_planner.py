from os import path

from tarski.benchmarks.blocksworld import generate_fstrips_blocksworld_problem
from tarski.benchmarks.counters import generate_fstrips_counters_problem

from fstripssmt.runner import run_on_problem
from tests.plan.common import reader, collect_strips_benchmarks

here = path.abspath(path.dirname(__file__))
benchmarks = path.abspath(path.join(here, '..', '..', 'benchmarks'))


def test_on_fstrips_bw():
    # Let's test the approach on one problem with non-numeric functions and nested expressions
    # (move(x, y) action has an add-effect $clear(loc(x))$
    problem = generate_fstrips_blocksworld_problem(
        nblocks=2,
        init=[('b1', 'b2'), ('b2', 'table')],
        goal=[('b2', 'table'), ('b1', 'table')]
    )
    assert run_on_problem(problem, reachability="none", max_horizon=1) == ['move(b1, table)']

    problem = generate_fstrips_blocksworld_problem(
        nblocks=2,
        init=[('b1', 'b2'), ('b2', 'table')],
        goal=[('b2', 'b1'), ('b1', 'table')]
    )
    #
    # assert run_on_problem(problem, reachability="none", max_horizon=1) is None

    assert run_on_problem(problem, reachability="none", max_horizon=2) == ['move(b1, table)', 'move(b2, b1)']

    problem = generate_fstrips_blocksworld_problem(
        nblocks=4,
        init=[('b1', 'b2'), ('b2', 'table'), ('b3', 'b4'), ('b4', 'table')],
        goal=[('b2', 'b3'), ('b3', 'b4'), ('b4', 'b1'), ('b1', 'table')]
    )
    assert 0


def test_on_counters():
    counters = generate_fstrips_counters_problem(ncounters=3)
    plan = run_on_problem(counters, reachability="none", max_horizon=4)
    assert plan


def test_on_blocks():
    instance_file, domain_file = collect_strips_benchmarks(["blocks:probBLOCKS-4-0.pddl"])[0]
    problem = reader().read_problem(domain_file, instance_file)

    plan = run_on_problem(problem, reachability="full", max_horizon=6)
    assert plan

    plan = run_on_problem(problem, reachability="full", max_horizon=5)
    assert plan is None  # Optimal plan has length 6


