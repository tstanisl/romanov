from romanov.solver import Solver
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

if __name__ == '__main__':
    unittest.main()
