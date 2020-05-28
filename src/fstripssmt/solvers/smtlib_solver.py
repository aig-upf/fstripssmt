import shutil
import time
from io import TextIOWrapper
from subprocess import Popen, PIPE

from pysmt.exceptions import UnknownSolverAnswerError, SolverReturnedUnknownResultError


class SetAwareSmtLibSolver:
    """
    Our own subclass of PySMT's SmtLibSolver with support for sets in models.
    """
    def __init__(self, solver_path, logic, debug_interaction=False):
        self.solver = Popen(solver_path, stdout=PIPE, stderr=PIPE, stdin=PIPE, bufsize=-1)
        self.logic = logic
        self.debug_interaction = debug_interaction

        # Give time to the process to start-up
        time.sleep(0.01)
        self.solver_stdin = TextIOWrapper(self.solver.stdin)
        self.solver_stdout = TextIOWrapper(self.solver.stdout)

    def _send_command(self, cmd):
        """Sends a command to the STDIN pipe."""
        self._debug("Sending: %s", cmd)
        self.solver_stdin.write(cmd)
        self.solver_stdin.write("\n")
        self.solver_stdin.flush()

    def _send_silent_command(self, cmd):
        """Sends a command to the STDIN pipe and awaits for acknowledgment."""
        self._send_command(cmd)
        self._check_success()

    def _get_answer(self):
        """Reads a line from STDOUT pipe"""
        res = self.solver_stdout.readline().strip()
        self._debug("Read: %s", res)
        return res

    def _check_success(self):
        res = self._get_answer()
        if res != "success":
            raise UnknownSolverAnswerError("Solver returned: '%s'" % res)

    def _debug(self, msg, *format_args):
        if self.debug_interaction:
            print(msg % format_args)

    def add_smtlib_command(self, command):
        self._send_silent_command(command)
        
    def solve(self):
        self._send_command("(check-sat)")
        ans = self._get_answer()
        if ans == "sat":
            return True
        elif ans == "unsat":
            return False
        elif ans == "unknown":
            raise SolverReturnedUnknownResultError
        else:
            raise UnknownSolverAnswerError("Solver returned: " + ans)

    def get_value(self, term):
        command = f'(get-value ({term}))'
        self._send_command(command)
        res = self.solver_stdout.readline().strip()
        # Let's parse the output with a quick and nice hack, since it's going to be always a boolean expression
        parse = res.replace(term, "").strip('() ')
        if parse == "false":
            return False
        elif parse == "true":
            return True
        else:
            raise RuntimeError(f"Unknown solver response: '{res}'")


def solve_smtlib(theory, solver_name, logic):
    """ """
    assert solver_name == "cvc4"

    commands = {
        'cvc4': [shutil.which('cvc4'), "--lang=smt2", "--print-success", "-m"],
    }

    solver = SetAwareSmtLibSolver(commands["cvc4"], logic)
    print(f'Using solver "{solver_name}" and logic "{logic}"')

    for line in theory.iterate_over_smtlib_declaration():
        solver.add_smtlib_command(line)

    # Let's rock
    res = solver.solve()
    if not res:
        return None
    return solver
