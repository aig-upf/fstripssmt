import tempfile

from pysmt.shortcuts import Solver, And


def solve(theory):
    """ """
    # with tempfile.NamedTemporaryFile(mode='w+t', delete=False) as f:
    #     for t in theory:
    #         print(t, file=f)
    #     print(f'Theory printed on file {f.name}')

    with Solver() as solver:
        # is_sat = solver.is_sat(And(theory))  # Alternatively

        for sentence in theory:
            solver.add_assertion(sentence)

        solvable = solver.solve()
        if not solvable:
            return None

        return solver.get_model()
