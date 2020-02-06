
class PlannerError(Exception):
    """ Common ancestor class to all of the planner's exceptions. """


class TransformationError(PlannerError):
    """ An error compiling a formula into an SMT theory. """
    pass
