"""
    Helper to run the planner
"""
import errno
import logging
import sys
import os
import argparse
import subprocess
from collections import OrderedDict
from pathlib import Path

from pysmt.shortcuts import get_unsat_core
from tarski.fstrips.manipulation.simplify import Simplify
from tarski.syntax.transform import compile_universal_effects_away
from tarski.io import FstripsReader, find_domain_filename
from tarski.syntax.transform.action_grounding import ground_schema_into_plain_operator_from_grounding
from tarski.utils import resources
from tarski.grounding import LPGroundingStrategy, NaiveGroundingStrategy

from fstripssmt.encodings.classical import ClassicalEncoding, linearize_parallel_plan
from fstripssmt.solvers.common import solve


def parse_arguments(args):
    parser = argparse.ArgumentParser(description='Solve a given instance.')
    parser.add_argument('-i', '--instance', required=True, help="The path to the problem instance file.")
    parser.add_argument('--domain', default=None, help="(Optional) The path to the problem domain file. If none is "
                                                       "provided, the system will try to automatically deduce "
                                                       "it from the instance filename.")

    parser.add_argument('--debug', action='store_true', help="Compile in debug mode.")
    parser.add_argument("--max-horizon", type=int, default=10,
                        help='The maximum (parallel) horizon that will be considered.')

    parser.add_argument("--reachability", help='The type of reachability analysis performed', default="full",
                        choices=('full', 'vars', 'none'))
    parser.add_argument('--planfile', default=None, help="(Optional) Path to the file where the solution plan "
                                                         "will be left.")

    args = parser.parse_args(args)
    return args


def extract_names(domain_filename, instance_filename):
    """ Extract the canonical domain and instance names from the corresponding filenames """
    domain = os.path.basename(os.path.dirname(domain_filename))
    instance = os.path.splitext(os.path.basename(instance_filename))[0]
    return domain, instance


def run_on_problem(problem, reachability, max_horizon):
    with resources.timing(f"Preprocessing problem", newline=True):
        # Both the LP reachability analysis and the backend expect a problem without universally-quantified effects
        problem = compile_universal_effects_away(problem)
        simplifier = Simplify(problem, problem.init)
        problem = simplifier.simplify()

    do_reachability = reachability != 'none'
    action_groundings = None  # Schemas will be ground in the backend
    if do_reachability:
        ground_actions = reachability == 'full'
        msg = "Computing reachable groundings " + ("(actions+vars)" if ground_actions else "(vars only)")
        with resources.timing(msg, newline=True):
            grounding = LPGroundingStrategy(problem, ground_actions=ground_actions, include_variable_inequalities=False)
            ground_variables = grounding.ground_state_variables()
            if ground_actions:
                action_groundings = grounding.ground_actions()
    else:
        with resources.timing(f"Computing naive groundings", newline=True):
            grounding = NaiveGroundingStrategy(problem, ignore_symbols={'total-cost'})
            ground_variables = grounding.ground_state_variables()
            action_groundings = grounding.ground_actions()

    statics, fluents = grounding.static_symbols, grounding.fluent_symbols

    if action_groundings:
        # Prune those action schemas that have no grounding at all
        for name, a in list(problem.actions.items()):
            if not action_groundings[name]:
                del problem.actions[name]

    # TODO Let's plan!

    operators = []
    for name, act in problem.actions.items():
        for grounding in action_groundings[name]:
            op = ground_schema_into_plain_operator_from_grounding(act, grounding)
            if reachability == 'full':
                operators.append(op)
            else:
                s = simplifier.simplify_action(op, inplace=True)
                if s is not None:
                    operators.append(s)

    encoding = ClassicalEncoding(problem, operators, ground_variables)

    theory = encoding.generate_theory(horizon=max_horizon)
    print(f"SMT Theory has {len(theory.constraints)} constraints")
    print("\n".join(map(str, theory.constraints)))
    model = solve(theory.constraints)

    if model is None:
        print(f"Could not solve problem under the given max. horizon")
        ucore = get_unsat_core(theory.constraints)
        print("UNSAT-Core size '%d'" % len(ucore))
        for f in ucore:
            print(f.serialize())

        return None

    plan = linearize_parallel_plan(encoding.extract_parallel_plan(model))
    print(f"Found length-{len(plan)} plan:")
    print('\n'.join(map(str, plan)))
    print("Model:")
    print(model)
    return plan


def run(args):
    # Determine the proper domain and instance filenames
    if args.domain is None:
        args.domain = find_domain_filename(args.instance)
        if args.domain is None:
            raise RuntimeError(f'Could not find domain filename that matches instance file "{args.instance}"')

    domain_name, instance_name = extract_names(args.domain, args.instance)
    print(f'Problem domain: "{domain_name}" ({os.path.realpath(args.domain)})')
    print(f'Problem instance: "{instance_name}" ({os.path.realpath(args.instance)})')

    with resources.timing(f"Parsing problem", newline=True):
        problem = parse_problem_with_tarski(args.domain, args.instance)

    plan = run_on_problem(problem, args.reachability, args.max_horizon)

    translation_dir = None
    # Validate the resulting plan:
    is_plan_valid = validate(args.domain, args.instance, os.path.join(translation_dir, 'first.plan'))

    return is_plan_valid


def validate(domain_name, instance_name, planfile):
    with resources.timing(f"Running validate", newline=True):
        plan = Path(planfile)
        if not plan.is_file():
            logging.info("No plan file could be found.")
            return -1

        validate_inputs = ["validate", domain_name, instance_name, planfile]

        try:
            _ = subprocess.call(' '.join(validate_inputs), shell=True)
        except OSError as err:
            if err.errno == errno.ENOENT:
                logging.error("Error: 'validate' binary not found. Is it on the PATH?")
                return -1
            else:
                logging.error("Error executing 'validate': {}".format(err))

    return 0


def parse_problem_with_tarski(domain_file, inst_file):
    reader = FstripsReader(raise_on_error=True, theories=None, strict_with_requirements=False)
    return reader.read_problem(domain_file, inst_file)


def main(args):
    args = parse_arguments(args)
    import logging
    logging.basicConfig(stream=sys.stdout, level=logging.DEBUG if args.debug else logging.INFO)
    return run(args)
