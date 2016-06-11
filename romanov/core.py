"Core primitives of Romanov environment"

from abc import ABCMeta, abstractmethod
import sys

class Encoder:
    "Encodes set of assumptions as SMTLIB2 query"

    def __init__(self):
        self._declares = []
        self._formulae = []
        self._cache = dict()
        self._assumes = []

    def _encode_cached(self, encodable, func):
        "Helper for decorator. Caches SMTLIB2 encoding of encodable"
        key = id(encodable)
        if key in self._cache:
            return self._cache[key][0]
        smt2name = func(encodable, self)
        self._cache[key] = (smt2name, encodable)
        return smt2name

    @staticmethod
    def cached(func):
        "Decorator that adds caching for func"
        def helper(encodable, encoder):
            "Decorated func"
            return Encoder._encode_cached(encoder, encodable, func)
        return helper

    def assume(self, root):
        """Add assume to the encoded formula.
        The argument root must be Bool."""
        root = Bool(root)
        self._assumes.append(root)

    def declare(self, smt2type):
        """Creates a new fresh variable of type smt2type.
           Returns label as string."""
        self._declares.append(smt2type)
        return 'D{}'.format(len(self._declares) - 1)

    def formula(self, formula):
        "Constructs new label from a given formula."
        self._formulae.append(formula)
        return 'F{}'.format(len(self._formulae) - 1)

    def encode(self):
        "Encoders all assumptions to SMTLIB2 query. Returns a (large) string."
        clauses = []
        assumes_copy = []
        while self._assumes:
            assume = self._assumes.pop()
            assumes_copy.append(assume)
            clause = assume.smt2_encode(self)
            clauses.append(clause)

        lines = ['(set-logic QF_AUFBV)']

        for idx, smt2type in enumerate(self._declares):
            line = '(declare-fun D{} () {})'.format(idx, smt2type)
            lines.append(line)

        lines.append('(assert')

        for idx, formula in enumerate(self._formulae):
            line = '  (len ((F{} {}))'.format(idx, formula)
            lines.append(line)

        lines.append('  (and true')

        lines.extend('    ' + clause for clasue in clauses)

        lines.append(')' * (len(self._formulae) + 2))

        self._assumes = assumes_copy

        return '\n'.join(lines)

class EncodableMeta(ABCMeta):
    "Metaclass used to decorate methods that are cached by Encoder"
    def __new__(mcs, name, bases, namespace):
        cls = ABCMeta.__new__(mcs, name, bases, namespace)
        cls.smt2_encode = Encoder.cached(cls.smt2_encode)
        return cls

class Encodable(metaclass=EncodableMeta):
    "Class dedicated for objects that can be translated to SMTLIB2"
    def __init__(self):
        pass

    @abstractmethod
    def smt2_encode(self, encoder):
        "Encodes objects in SMTLIB2"

class Fresh(Encodable):
    "Fresh symbols."
    def __init__(self, smt2_type):
        super().__init__()
        self.smt2_type = smt2_type

    def smt2_encode(self, encoder):
        return encoder.declare(self, self.smt2_type)

class Opcode(Encodable):
    "Abstraction of result of SMTLIB2 operation"
    def __init__(self, smt2op, *args):
        super().__init__()
        self.smt2op = smt2op
        self.args = args

    def smt2_encode(self, encoder):
        args = [encoder.encode(arg) for arg in self.args]
        formula = '({} {})'.format(self.smt2op, ' '.join(args))
        return encoder.formula(self, formula)

class Symbolic(Encodable):
    "Abstract class for symbolic classes in Romanov"
    literals = ()
    def __init__(self, value):
        super().__init__()

        if isinstance(value, Symbolic):
            value = value.value

        if not isinstance(value, (Fresh, Opcode) + self.literals):
            TypeError('Valuee is non-compatible')

        self.value = value

    def smt2_encode(self, encoder):
        return encoder.encode(self.value)

class Bool(Symbolic):
    "Abstraction of symbolic boolean variable"
    literals = (bool,)
    def __init__(self, value=None):
        if value is None:
            value = Fresh('Bool')
        super().__init__(value)

    def smt2_encode(self, encoder):
        if self.value is True:
            return 'true'
        if self.value is False:
            return 'false'
        return super().smt2_encode(encoder)

    @staticmethod
    def _operator(smt2op, *args):
        "Helper for implementing operators"
        try:
            args = [Bool(arg) for arg in args]
            value = Opcode(smt2op, *args)
            return Bool(value)
        except TypeError:
            print(sys.exc_info())
            return NotImplemented

    def __eq__(self, arg):
        return self._operator('=', self, arg)

    def __ne__(self, arg):
        return self._operator('distinct', self, arg)
