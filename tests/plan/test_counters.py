
from tarski.benchmarks.counters import generate_fstrips_counters_problem

from fstripssmt.runner import run_on_problem


def test_counters():
    counters = generate_fstrips_counters_problem(ncounters=3)
    plan = run_on_problem(counters, reachability="none")
    assert plan
