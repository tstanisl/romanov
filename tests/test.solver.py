"Unit tests for SMTLIB2 solvers for romanov package"
from romanov.solver import Solver, DumpSolver
import io
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

if __name__ == '__main__':
    unittest.main()
