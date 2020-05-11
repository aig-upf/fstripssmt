
from pysmt.shortcuts import Solver


def solve(theory, solver_name):
    """ """
    # with tempfile.NamedTemporaryFile(mode='w+t', delete=False) as f:
    #     for t in theory:
    #         print(t, file=f)
    #     print(f'Theory printed on file {f.name}')

    # with Solver(logic="UFIDL") as solver:
    with Solver(name=solver_name) as solver:
        # is_sat = solver.is_sat(And(theory))  # Alternatively

        print(f'Using solver "{solver_name}" configured with logic {solver.logic}')

        for sentence in theory:
            solver.add_assertion(sentence)

        solvable = solver.solve()
        if not solvable:
            return None

        return solver.get_model()
