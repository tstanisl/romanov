"Unit tests for SMTLIB2 solvers for romanov package"
from romanov.solver import Solver, DumpSolver, PipeSolver
import io
import sys
import unittest

class SolverTest(unittest.TestCase):
    "Tests API of base romanov.Solver class."
    def test_has_model(self):
        "Check if Solver generates model."
        solver = Solver()
        self.assertTrue(solver.has_model)

        solver = Solver(has_model=True)
        self.assertTrue(solver.has_model)

        solver = Solver(has_model=False)
        self.assertFalse(solver.has_model)

    def test_emit(self):
        "Check if emit() is not implemented."
        solver = Solver()
        with self.assertRaises(NotImplementedError):
            solver.emit('')

    def test_recv(self):
        "Check if recv() is not implemented."
        solver = Solver()
        with self.assertRaises(NotImplementedError):
            solver.recv()

class DumpSolverTest(unittest.TestCase):
    "Tests API of base romanov.DumpSolver class."
    def test_has_model(self):
        "Check if DumpSolver generates no model."
        stream = io.StringIO()
        solver = DumpSolver(stream)
        self.assertFalse(solver.has_model)

    def test_reset(self):
        "Check if reset() works."
        stream = io.StringIO(newline='')
        solver = DumpSolver(stream)
        solver.reset()
        smt = '(set-logic QF_AUFBV)\n'
        self.assertTrue(stream.getvalue() == smt)

    def test_recv(self):
        "Check if recv() returns unknown."
        stream = io.StringIO(newline='')
        solver = DumpSolver(stream)
        ans = solver.recv()
        self.assertTrue(ans == 'unknown')

    def test_emit(self):
        "Check if emit() adds newlined clause to stream."
        stream = io.StringIO(newline='')
        solver = DumpSolver(stream)
        solver.emit('hello')
        solver.emit('world')
        smt = 'hello\nworld\n'
        self.assertTrue(stream.getvalue() == smt)

class PipeSolverTest(unittest.TestCase):
    "Tests API of base romanov.PipeSolver class."

    # cmdline used to run echo process
    echo_py = (sys.executable, '-c', 'while True: print(input())')

    def test_bad_path(self):
        "Check if bad path raises."
        solver = PipeSolver('.')
        with self.assertRaises(PermissionError):
            solver.reset()

    def test_echo(self):
        "Check if echoing works."
        solver = PipeSolver(self.echo_py)
        solver.reset()
        # skip (set-logic X)
        solver.recv()

        solver.emit('123')
        solver.emit('456')
        ans1 = solver.recv()
        ans2 = solver.recv()

        self.assertTrue(ans1 == '123')
        self.assertTrue(ans2 == '456')

    def test_reset(self):
        "Check if reset() works by invalidating old emit()."
        solver = PipeSolver(self.echo_py)
        solver.reset()

        solver.emit('123')

        solver.reset()
        # skip (set-logic X)
        solver.recv()

        solver.emit('456')
        ans = solver.recv()

        # 123 should be discarded by reset()
        self.assertTrue(ans == '456')

    def test_logic(self):
        "Check if SMTLIB2 logic is correctly set"
        solver = PipeSolver(self.echo_py, logic="123")
        solver.reset()
        ans = solver.recv()
        self.assertTrue(ans == '(set-logic 123)')

    def test_has_model(self):
        "Check if has_model works."
        solver = PipeSolver(self.echo_py, has_model=False)
        self.assertFalse(solver.has_model)

        solver = PipeSolver(self.echo_py, has_model=True)
        self.assertTrue(solver.has_model)

    def test_env(self):
        "Check if env works."
        env_py = 'import os; print(os.environ["MAGIC"])'
        args = (sys.executable, '-c', env_py)
        solver = PipeSolver(args, env={'MAGIC' : 'SEZAM'})
        solver.reset()
        ans = solver.recv()
        self.assertTrue(ans == 'SEZAM')

    def test_options(self):
        "Check if options work."
        options = {'ABC' : '123', 'DEF' : 456}
        solver = PipeSolver(self.echo_py, options=options)
        expected = {'(set-option :{} {})'.format(key, val)
                    for key, val in options.items()}

        solver.reset()

        ans1 = solver.recv()
        ans2 = solver.recv()

        received = {ans1, ans2}

        self.assertTrue(received == expected)

if __name__ == '__main__':
    unittest.main()
