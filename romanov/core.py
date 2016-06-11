"Core primitives of Romanov environment"

from abc import ABCMeta, abstractmethod
from collections import OrderedDict, namedtuple
import sys

class Encoder:
    "Encodes Symbolics as SMTLIB2"
    Entry = namedtuple('EncoderEntry', ['name', 'ref', 'smt2'])

    def __init__(self):
        self._cache = OrderedDict()
        self._assumes = []

    def _cache_add(self, entry):
        "Add entry to the cache indexed by ref"
        key = id(entry.ref)
        self._cache[key] = entry

    def _cache_find(self, ref):
        "Checks if ref was added to cache. Return label or None."
        key = id(ref)
        if key in self._cache:
            return self._cache[key].name
        return None

    def assume(self, root):
        """Add assume to the encoded formula.
        The argument root must be Bool."""
        root = Bool(root)
        self._assumes.append(root)

    def declare(self, ref, smt2type):
        """Creates a new fresh variable of type smt2type.
           Returns label as string."""
        name = self._cache_find(ref)
        if name is not None:
            return name

        name = 'D{}'.format(len(self._cache))
        smt2 = '(declare-fun {} () {})'.format(name, smt2type)
        entry = Encoder.Entry(name, ref, smt2)

        self._cache_add(entry)

        return name

    def formula(self, ref, formula):
        "Constructs new label from given formula"
        ret = self._cache_find(ref)
        if ret is not None:
            return ret

        name = 'L{}'.format(len(self._cache))
        entry = Encoder.Entry(name, ref, formula)

        self._cache_add(entry)

        return name

    @classmethod
    def cached(cls, func):
        "Decorator that adds caching for func"
        print('Decorated', func)
        return func

    def encode(self, value):
        """Encodes value as SMTLIB2.
           Value must be Encodable.
           Returns SMTLIB2 label as string."""
        ret = self._cache_find(value)
        if ret is not None:
            return ret

        assert isinstance(value, Encodable)

        return value.smt2_encode(self)

    def run(self):
        "Translates assumptions to SMTLIB2 query. Returns (large) string."
        clauses = []
        while self._assumes:
            root = self._assumes.pop()
            result = self.encode(root)
            clauses.append(result)

        lines = ['(set-logic QF_AUFBV)']

        for name, _, smt2 in self._cache.values():
            if name.startswith('D'):
                lines.append(smt2)

        mark = len(lines)
        lines.append('(assert')
        for name, _, smt2 in self._cache.values():
            if name.startswith('L'):
                line = '  (let (({} {}))'.format(name, smt2)
                lines.append(line)
        lines.append('  (and true')
        n_brackets = len(lines) - mark

        lines += ['       ' + clause for clause in clauses]
        line = ')' * n_brackets
        lines.append(line)

        # reset encoder
        self._cache = {}
        self._assumes = []

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
