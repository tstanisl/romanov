from romanov.solver import Solver, DumpSolver
import io
import unittest

class SolverTest(unittest.TestCase):
    def test_has_model(self):
        s = Solver()
        self.assertTrue(s.has_model)

        s = Solver(has_model = True)
        self.assertTrue(s.has_model)

        s = Solver(has_model = False)
        self.assertFalse(s.has_model)

    def test_emit(self):
        s = Solver()
        with self.assertRaises(NotImplementedError):
            s.emit('')

    def test_recv(self):
        s = Solver()
        with self.assertRaises(NotImplementedError):
            s.recv()

class DumpSolverTest(unittest.TestCase):
    def test_init(self):
        f = io.StringIO()
        s = DumpSolver(f)

    def test_reset(self):
        f = io.StringIO(newline = '')
        s = DumpSolver(f)
        s.reset()
        smt = '(set-logic QF_AUFBV)\n'
        self.assertTrue(f.getvalue() == smt)

    def test_recv(self):
        f = io.StringIO(newline = '')
        s = DumpSolver(f)
        ans = s.recv()
        self.assertTrue(ans == 'unknown')

    def test_emit(self):
        f = io.StringIO(newline = '')
        s = DumpSolver(f)
        s.emit('hello')
        s.emit('world')
        smt = 'hello\nworld\n'
        self.assertTrue(f.getvalue() == smt)
    def test_emit(self):
        f = io.StringIO(newline = '')
        s = DumpSolver(f)
        s.emit('hello')
        s.emit('world')
        smt = 'hello\nworld\n'
        self.assertTrue(f.getvalue() == smt)

if __name__ == '__main__':
    unittest.main()
