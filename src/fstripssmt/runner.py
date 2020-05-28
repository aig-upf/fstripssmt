"""
    Helper to run the planner
"""
import errno
import logging
import sys
import os
import argparse
import subprocess
from pathlib import Path

from tarski import Variable
from tarski.fstrips.manipulation.simplify import Simplify
from tarski.grounding.ops import approximate_symbol_fluency
from tarski.syntax import QuantifiedFormula, Quantifier, lor, land
from tarski.syntax.formulas import is_and
from tarski.syntax.ops import free_variables
from tarski.syntax.transform import compile_universal_effects_away, remove_quantifiers, QuantifierEliminationMode
from tarski.io import FstripsReader, find_domain_filename
from tarski.syntax.transform.substitutions import term_substitution, create_substitution
from tarski.theories import has_theory, Theory
from tarski.utils import resources

from fstripssmt.encodings.lifted import FullyLiftedEncoding
from fstripssmt.solvers.common import solve
from .errors import TransformationError
from .solvers.smtlib import SMTLIBTranslator
from .solvers.pysmt import PySMTTranslator, linearize_parallel_plan, compute_signature_bindings
from .solvers.smtlib_solver import solve_smtlib


def parse_arguments(args):
    parser = argparse.ArgumentParser(description='Solve a given instance.')
    parser.add_argument('-i', '--instance', required=True, help="The path to the problem instance file.")
    parser.add_argument('--domain', default=None, help="(Optional) The path to the problem domain file. If none is "
                                                       "provided, the system will try to automatically deduce "
                                                       "it from the instance filename.")

    parser.add_argument('--debug', action='store_true', help="Compile in debug mode.")
    parser.add_argument('--print-model', action='store_true', help="Print full model found by SMT solver, if any.")

    parser.add_argument("-H", "--max-horizon", type=int, default=1,
                        help='The maximum (parallel) horizon that will be considered.')

    # parser.add_argument("--reachability", help='The type of reachability analysis performed', default="full",
    #                     choices=('full', 'vars', 'none'))

    parser.add_argument("--grounding", help='The type of grounding to be performed', default="none",
                        choices=('full', 'none'))

    parser.add_argument("--solver", help='The preferred SMT solver. Note that not all solvers accept all encodings',
                        default="z3",
                        choices=('msat', 'cvc4', 'yices', 'z3', 'picosat'))

    parser.add_argument("--smtlib",
                        help='A filename to dump the encoding in SMTLIB format. Use None to skip the dumping',
                        default="theory.smtlib")

    parser.add_argument('--planfile', default=None, help="(Optional) Path to the file where the solution plan "
                                                         "will be left.")

    args = parser.parse_args(args)
    args.reachability = 'none'  # Currently disabled
    return args


def extract_names(domain_filename, instance_filename):
    """ Extract the canonical domain and instance names from the corresponding filenames """
    domain = os.path.basename(os.path.dirname(domain_filename))
    instance = os.path.splitext(os.path.basename(instance_filename))[0]
    return domain, instance


def enumerate_substitutions(variables, horizon):
    """ Enumerates all possible substitutions for the given variables.
    TODO Note that this is a hacky rewriting of the corresponding Tarski method, which we need in order
         to properly account for the timestep integer type, that we cannot bound at the moment.
         When that is fixed, we can simply remove this method and use instead:
    >>> from tarski.syntax.transform.substitutions import enumerate_substitutions
    """
    assert len(variables) > 0 and all(isinstance(var, Variable) for var in variables)
    lang = variables[0].language
    for values in compute_signature_bindings(lang, [v.sort for v in variables], horizon):
        yield create_substitution(variables, values)


def fully_ground(smtlang, f, horizon):
    phi = remove_quantifiers(smtlang, f, QuantifierEliminationMode.All)
    phi = Simplify().simplify_expression(phi)
    if phi is False:
        raise RuntimeError(f'Formula {phi} simplified to False, hence the theory is not satisfiable')
    return phi

    # if not isinstance(f, QuantifiedFormula):
    #     return f
    #
    # clauses = []
    # for subst in enumerate_substitutions(f.variables, horizon):
    #     clauses.append(fully_ground(term_substitution(f.formula, subst, inplace=False), horizon))
    #
    # connective = lor if f.quantifier == Quantifier.Exists else land
    # return connective(*clauses, flat=True)


def choose_translator_based_on_theory(smtlang):
    return SMTLIBTranslator if has_theory(smtlang, "sets") else PySMTTranslator


def run_on_problem(problem, reachability, max_horizon, grounding, smtlib_filename=None, solver_name='z3',
                   print_full_model=False):
    """ Note that invoking this method might perform several modifications and simplifications to the given problem
    and its language """
    with resources.timing(f"Preprocessing problem", newline=True):
        # The encoding expects a problem without universally-quantified effects, so let's compile them away
        problem = compile_universal_effects_away(problem, inplace=True)

        # Let's also some apply trivial simplifications
        simplifier = Simplify(problem, problem.init)
        problem = simplifier.simplify(inplace=True, remove_unused_symbols=True)

        # Compute which symbols are static
        _, statics = approximate_symbol_fluency(problem)

    # ATM we disable reachability, as it's not being used for the lifted encoding
    # do_reachability_analysis(problem, reachability)

    # Let's just fix one single horizon value, for the sake of testing
    horizon = max_horizon

    # Ok, down to business: let's generate the theory, which will be represented as a set of first-order sentences
    # in a different Tarski FOL (smtlang):
    with resources.timing(f"Generating theory", newline=True):
        encoding = FullyLiftedEncoding(problem, statics)
        smtlang, formulas, comments = encoding.generate_theory(horizon=horizon)

    if grounding == 'full':
        comments, formulas = ground_smt_theory(smtlang, comments, formulas, horizon)

    # Some sanity check: All formulas must be sentences!
    for formula in formulas:
        freevars = free_variables(formula)
        if freevars:
            raise TransformationError(f'Formula {formula} has unexpected free variables: {freevars}')

    # Once we have the theory in Tarski format, let's just translate it into PySMT format:
    with resources.timing(f"Translating theory to pysmt", newline=True):
        anames = set(a.name for a in problem.actions.values())

        translator_class = choose_translator_based_on_theory(smtlang)
        translator = translator_class(smtlang, statics, anames)
        translated = translator.translate(formulas)

        # Let's simplify the sentences for further clarity
        translated = translator.simplify(translated)

    # Some optional debugging statements:
    # _ = [print(f"{i}. {s}") for i, s in enumerate(formulas)]
    # _ = [print(f"{i}. {s.serialize()}") for i, s in enumerate(translated)]
    # _ = [print(f"{i}. {to_smtlib(s, daggify=False)}") for i, s in enumerate(translated)]

    # Try some built-in quantifier elimination?
    # translated = [qelim(t, solver_name="z3", logic="LIA") for t in translated]

    # Dump the SMT theory
    if smtlib_filename is not None:
        with resources.timing(f"Writing theory to file \"{smtlib_filename}\"", newline=True):
            with open(smtlib_filename, "w") as f:
                translator.print_as_smtlib(translated, comments, f)

    with resources.timing(f"Solving theory", newline=True):
        if Theory.SETS in smtlang.theories:
            smtlib_solver = solve_smtlib(translated, solver_name, logic="QF_UFLIAFS")
            plan = decode_satlib_model(smtlib_solver, horizon, translator, print_full_model)
        else:
            model = solve(translated, solver_name)
            plan = decode_smt_model(model, horizon, translator, print_full_model)
    if plan:
        print(f"Found length-{len(plan)} plan:")
        print('\n'.join(map(str, plan)))
    return plan


def ground_smt_theory(smtlang, comments, formulas, horizon):
    with resources.timing(f"Grounding theory", newline=True):

        # First ground the quantifiers, and rule out results that are True
        formulas = list(filter(lambda x: x is not True,
                               (fully_ground(smtlang, f, horizon) for f in formulas)))

        # Now reindex the comments and "unwrap" conjunctions assert A and B
        # into two different assertions assert A; assert B
        ground = []
        reindexed_comments = dict()
        unwrap_conjunction = lambda phi: phi.subformulas if is_and(phi) else [phi]
        for i, f in enumerate(formulas, start=0):
            if i in comments:
                reindexed_comments[len(ground)] = comments[i]
            ground += unwrap_conjunction(f)
        formulas = ground
        comments = reindexed_comments
    return comments, formulas


def decode_smt_model(smtlib_solver, horizon, translator, print_full_model):
    if smtlib_solver is None:
        print(f"Could not solve problem under given horizon {horizon}")
        # ucore = get_unsat_core(translated)
        # print(f"Showing unsat core of size {len(ucore)}:")
        # for f in ucore:
        #     print(f.serialize())
        return None

    return linearize_parallel_plan(translator.extract_parallel_plan(smtlib_solver, horizon, print_full_model))


def decode_satlib_model(model, horizon, translator, print_full_model):
    if model is None:
        print(f"Could not solve problem under given horizon {horizon}")
        # ucore = get_unsat_core(translated)
        # print(f"Showing unsat core of size {len(ucore)}:")
        # for f in ucore:
        #     print(f.serialize())
        return None

    return linearize_parallel_plan(translator.extract_parallel_plan(model, horizon, print_full_model))


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

    plan = run_on_problem(problem, args.reachability, args.max_horizon, args.grounding, args.smtlib, args.solver,
                          args.print_model)

    if not plan:
        return

    # If we found a plan, we validate it
    planfile = os.path.realpath("plan.out")
    with open(planfile, "w") as f:
        print('\n'.join(plan), file=f)
        print(f'Plan printed to file "{f.name}"')
        is_plan_valid = validate(args.domain, args.instance, f.name)

    return is_plan_valid


def validate(domain_name, instance_name, planfile):
    with resources.timing(f"Running validate", newline=True):
        plan = Path(planfile)
        if not plan.is_file():
            logging.info("No plan file could be found.")
            return -1

        validate_inputs = ["validate", domain_name, instance_name, planfile]

        try:
            # print("Executing: ", ' '.join(validate_inputs))
            # _ = subprocess.call('which validate', shell=True)
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
