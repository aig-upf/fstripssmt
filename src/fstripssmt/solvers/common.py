
from pysmt.shortcuts import Solver
from tarski.theories import has_theory
from tarski.syntax.ops import compute_sort_id_assignment


class SMTTranslator:
    def __init__(self, smtlang, static_symbols, action_names):
        self.smtlang = smtlang
        self.static_symbols = static_symbols
        self.action_names = action_names

        assert has_theory(smtlang, "arithmetic")

        # Compute a sort-contiguous object ID assignment
        self.sort_bounds, self.object_ids = compute_sort_id_assignment(self.smtlang)


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
