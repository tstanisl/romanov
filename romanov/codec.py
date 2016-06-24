from abc import ABCMeta, abstractmethod
from functools import wraps

class Codec:
    "Encodes set of assumptions as SMTLIB2 query"

    def __init__(self):
        self._declares = []
        self._formulae = []
        self._cache = dict()
        self._assumes = []

    def cached_encode(self, encodable, func):
        """Caches SMTLIB2 encoding of encodable.
        The encoding is generated using func.
        Returns string."""
        key = id(encodable)
        if key in self._cache:
            return self._cache[key][0]
        smt2name = func(encodable, self)
        self._cache[key] = (smt2name, encodable)
        return smt2name

    def assume(self, root):
        """Add assume to the encoded formula.
        The argument root must be Bool."""
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
        "Codecs all assumptions to SMTLIB2 query. Returns a (large) string."
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
            line = '  (let ((F{} {}))'.format(idx, formula)
            lines.append(line)

        lines.append('  (and true')

        lines.extend('    ' + clause for clause in clauses)

        lines.append(')' * (len(self._formulae) + 2))

        lines.append('(check-sat)')

        self._assumes = assumes_copy

        return '\n'.join(lines)

class CodecableMeta(ABCMeta):
    "Metaclass used to decorate methods that are cached by Codec"
    def __new__(mcs, name, bases, namespace):
        cls = ABCMeta.__new__(mcs, name, bases, namespace)
        # dereference to avoid infinite recursion if decorated smt2_encode
        # is called via cls.smt2_encode
        to_wrap = cls.smt2_encode
        @wraps(to_wrap)
        def __wrapper(encodable, encoder):
            "Decorated smt2_encode"
            return encoder.cached_encode(encodable, to_wrap)
        cls.smt2_encode = __wrapper
        return cls

class Codecable(metaclass=CodecableMeta):
    "Class dedicated for objects that can be translated to SMTLIB2"
    def __new__(cls, *_):
        return super(Codecable, cls).__new__(cls)

    def __init__(self):
        pass

    @abstractmethod
    def smt2_encode(self, encoder):
        "Encodes objects in SMTLIB2"


