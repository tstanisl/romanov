"Unit tests for core classes and methods of Romanov package"

from romanov.core import current, make_current, Context
import unittest

class CurrentTest(unittest.TestCase):
    "Tests for setting/getting active Romanov context."

    def test_make_current(self):
        "Check if make_current() accepts context."
        context = Context()
        make_current(context)
        self.assertTrue(current() == context)

    def test_make_current_none(self):
        "Check if make_current() accepts None."
        make_current(None)
        self.assertTrue(current() == None)

    def test_make_current_ret(self):
        "Check if make_current() returns previous context."
        context1 = Context()
        context2 = Context()
        make_current(context1)
        old = make_current(context2)
        self.assertTrue(old == context1)

    def test_make_current_bad_type(self):
        "Check if make_current() rejects non-context."
        with self.assertRaises(TypeError):
            make_current(42)

if __name__ == '__main__':
    unittest.main()
