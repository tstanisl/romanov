from abc import ABCMeta, abstractmethod
from functools import wraps
from romanov.smt2aux import smt2_to_int

class Codec:
    "Encodes set of assumptions as SMTLIB2 query"

    def __init__(self, solver):
        self._solver = solver
        self._declares = []
        self._formulae = []
        self._encode_cache = dict()
        self._decode_cache = dict()
        self._assumes = []

    def cached_encode(self, codecable, func):
        """Caches SMTLIB2 encoding of codecable.
        The encoding is generated using func.
        Returns string."""
        key = id(codecable)
        if key in self._encode_cache:
            return self._encode_cache[key][0]
        smt2name = func(codecable, self)
        self._encode_cache[key] = (smt2name, codecable)
        return smt2name

    def cached_decode(self, codecable, func):
        """Caches SMTLIB2 decoding of codecable.
        The decoding is generated using func.
        Returns string."""
        key = id(codecable)
        if key in self._decode_cache:
            return self._decode_cache[key][0]
        smt2name = func(codecable, self)
        self._decode_cache[key] = (smt2name, codecable)
        return smt2name

    def assume(self, root):
        """Add assume to the encoded formula.
        The argument root must be Bool."""
        from romanov.core import Bool
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

    def _encode(self):
        "Codecs all assumptions to SMTLIB2 query. Returns a (large) string."
        clauses = []
        assumes_copy = []
        while self._assumes:
            assume = self._assumes.pop()
            assumes_copy.append(assume)
            clause = assume.smt2_encode(self)
            clauses.append(clause)

        emit = self._solver.emit

        emit('(set-logic QF_AUFBV)')

        for idx, smt2type in enumerate(self._declares):
            line = '(declare-fun D{} () {})'.format(idx, smt2type)
            emit(line)

        emit('(assert')

        for idx, formula in enumerate(self._formulae):
            line = '  (let ((F{} {}))'.format(idx, formula)
            emit(line)

        emit('  (and true')

        for line in ('    ' + clause for clause in clauses):
            emit(line)

        emit(')' * (len(self._formulae) + 2))

        self._assumes = assumes_copy

    def solve(self):
        self._encode()
        self._solver.emit('(check-sat)')
        ans = self._solver.recv()
        return ans

    def get_value(self, label):
        smt2 = '(get-value ({}))'.format(label)
        self._solver.emit(smt2)
        ans = self._solver.recv()
        return smt2_to_int(ans)

class CodecableMeta(ABCMeta):
    "Metaclass used to decorate methods that are cached by Codec"
    def __new__(mcs, name, bases, namespace):
        cls = ABCMeta.__new__(mcs, name, bases, namespace)
        # dereference to avoid infinite recursion if decorated smt2_encode
        # is called via cls.smt2_encode
        @wraps(cls.smt2_encode)
        def wrapper(codecable, encoder, _func=cls.smt2_encode):
            "Decorated smt2_encode"
            return encoder.cached_encode(codecable, _func)
        cls.smt2_encode = wrapper

        @wraps(cls.smt2_decode)
        def wrapper(codecable, decoder, _func=cls.smt2_decode):
            "Decorated smt2_decode"
            return decoder.cached_decode(codecable, _func)
        cls.smt2_decode = wrapper

        return cls

class Codecable(metaclass=CodecableMeta):
    "Class dedicated for objects that can be translated to SMTLIB2"

    def __init__(self):
        pass

    @abstractmethod
    def smt2_encode(self, codec):
        "Encodes objects in SMTLIB2"

    @abstractmethod
    def smt2_decode(self, codec):
        "Decodes objects from SMTLIB2"
