from os import path

from tarski.benchmarks.counters import generate_fstrips_counters_problem
from tarski.io import find_domain_filename

from fstripssmt.runner import run_on_problem
from tests.plan.common import reader, collect_strips_benchmarks

here = path.abspath(path.dirname(__file__))
benchmarks = path.abspath(path.join(here, '..', '..', 'benchmarks'))


def test_on_blocks():
    instance_file, domain_file = collect_strips_benchmarks(["blocks:probBLOCKS-4-0.pddl"])[0]
    instance_file = path.join(benchmarks, 'blocks', 'p02.pddl')
    domain_file = find_domain_filename(instance_file)
    problem = reader().read_problem(domain_file, instance_file)

    plan = run_on_problem(problem, reachability="full")
    assert plan


# def test_on_counters():
#     counters = generate_fstrips_counters_problem(ncounters=3)
#     plan = run_on_problem(counters, reachability="none")
#     assert plan
