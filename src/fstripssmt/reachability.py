from tarski.fstrips.manipulation import Simplify
from tarski.grounding import LPGroundingStrategy, NaiveGroundingStrategy
from tarski.syntax.transform.action_grounding import ground_schema_into_plain_operator_from_grounding
from tarski.utils import resources


def do_reachability_analysis(problem, reachability):
    # ATM This is not being used

    do_reachability = reachability != 'none'

    if do_reachability:
        ground_actions = reachability == 'full'
        msg = "Computing reachable groundings " + ("(actions+vars)" if ground_actions else "(vars only)")
        with resources.timing(msg, newline=True):
            grounding = LPGroundingStrategy(problem, ground_actions=ground_actions, include_variable_inequalities=False)
            ground_variables = grounding.ground_state_variables()
            if ground_actions:
                action_groundings = grounding.ground_actions()
                # Prune those action schemas that have no grounding at all
                for name, a in list(problem.actions.items()):
                    if not action_groundings[name]:
                        del problem.actions[name]
    else:
        with resources.timing(f"Computing naive groundings", newline=True):
            grounding = NaiveGroundingStrategy(problem, ignore_symbols={'total-cost'})
            ground_variables = grounding.ground_state_variables()
            action_groundings = grounding.ground_actions()

    statics, fluents = grounding.static_symbols, grounding.fluent_symbols
    simplifier = Simplify(problem, problem.init)
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