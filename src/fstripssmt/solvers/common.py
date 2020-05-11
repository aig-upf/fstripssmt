import tempfile

from pysmt.shortcuts import Solver, And


def solve(theory):
    """ """
    # with tempfile.NamedTemporaryFile(mode='w+t', delete=False) as f:
    #     for t in theory:
    #         print(t, file=f)
    #     print(f'Theory printed on file {f.name}')

    # with Solver(logic="UFIDL") as solver:
    with Solver(name="yices") as solver:
    # with Solver(name="z3") as solver:
        # is_sat = solver.is_sat(And(theory))  # Alternatively

        print(f'Using solver configured with logic {solver.logic}')

        for sentence in theory:
            solver.add_assertion(sentence)

        solvable = solver.solve()
        if not solvable:
            return None

        return solver.get_model()
