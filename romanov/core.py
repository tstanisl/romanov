"Core primitives of Romanov environment"

from romanov.codec import Codecable
from abc import abstractmethod
import sys

#pylint: disable=too-few-public-methods

class Fresh(Codecable):
    "Fresh symbols."
    def __init__(self, smt2_type):
        super().__init__()
        self.smt2_type = smt2_type

    def smt2_encode(self, encoder):
        return encoder.declare(self.smt2_type)

def make_value(cls, *args, **kvargs):
    """Produces a new value. Type cls must have get_key() class method.
       The method should return value based on args/kvargs that
       precisely define object among other cls-objects.
       Uses caching therefore returns the same object if
       called with the same arguments."""
    if not hasattr(make_value, 'cache'):
        make_value.cache = {}
    cache = make_value.cache

    key = (cls,) + cls.get_key(*args, **kvargs)
    if key in cache:
        print('; reused', key, '->', cache[key])
        return cache[key]

    instance = cls.make_value(*args, **kvargs)
    cache[key] = instance
    print('; cached', key, '->', instance)
    return instance

class Opcode(Codecable):
    "Abstraction of result of SMTLIB2 operation"
    def __init__(self, smt2op, *args):
        super().__init__()
        self.smt2op = smt2op
        self.args = args

    @classmethod
    def get_key(cls, smt2op, *args):
        "Computes a unique key from arguments of contructor."
        return (smt2op,) + tuple(repr(arg.value) for arg in args)

    @classmethod
    def make_value(cls, *args, **kvargs):
        "Create value of Opcode. May apply simplifications."
        return cls(*args, **kvargs)

    def smt2_encode(self, encoder):
        args = [arg.smt2_encode(encoder) for arg in self.args]
        formula = '({} {})'.format(self.smt2op, ' '.join(args))
        return encoder.formula(formula)

class IteOpcode(Opcode):
    def __init__(self, cond, arg0, arg1):
        super().__init__('ite', cond, arg0, arg1)

    @classmethod
    def get_key(cls, *args):
        return super().get_key('ite', *args)

    @classmethod
    def make_value(cls, cond, arg0, arg1):
        if arg0.value is arg1.value:
            return arg0
        if cond.value is True:
            return arg0
        if cond.value is False:
            return arg1
        return cls(cond, arg0, arg1)

class Symbolic(Codecable):
    "Abstract class for symbolic classes in Romanov"
    def __init__(self, value):
        super().__init__()

        if isinstance(value, Symbolic):
            value = value.value

        self.value = value

    def smt2_encode(self, encoder):
        return self.value.smt2_encode(encoder)

    @classmethod
    def ite(cls, cond, arg0, arg1):
        "If-then-else operator."
        cond = Bool(cond)
        arg0 = cls(arg0)
        arg1 = cls(arg1)
        return make_value(IteOpcode, cond, arg0, arg1)

class Bool(Symbolic):
    "Abstraction of symbolic boolean variable"
    def __init__(self, value=None):
        if value is None:
            value = Fresh('Bool')

        types = (Fresh, Opcode, Bool, bool)
        if not isinstance(value, types):
            raise TypeError('value type is incompatible with Bool')

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
            value = make_value(Opcode, smt2op, *args)
            return Bool(value)
        except TypeError:
            print(sys.exc_info())
            return NotImplemented

    def __eq__(self, arg):
        return self._operator('=', self, arg)

    def __ne__(self, arg):
        return self._operator('distinct', self, arg)

    def __or__(self, arg):
        return self._operator('or', self, arg)
    __ror__ = __or__

    def __and__(self, arg):
        return self._operator('and', self, arg)
    __rand__ = __and__

    def __rshift__(self, arg):
        return self._operator('=>', self, arg)

    def __rrshift__(self, arg):
        return self._operator('=>', arg, self)

    def __neg__(self):
        return self._operator('not', self)

class BitVecBase(Symbolic):
    "Base class for all bit vector classes."
    def __init__(self, value=None):
        bits = len(self)

        if value is None:
            smt2type = '(_ BitVec {})'.format(bits)
            value = Fresh(smt2type)

        cls = BitVecClass(bits)
        types = (Fresh, Opcode, cls, int)
        if not isinstance(value, types):
            raise TypeError('value is not compatible with ' + str(cls))

        if isinstance(value, int) and (value < 0 or value >= 2**bits):
            raise ValueError('value can not be represented by ' + str(cls))

        super().__init__(value)

    def smt2_encode(self, encoder):
        if isinstance(self.value, int):
            return '(_ bv{} {})'.format(self.value, len(self))
        return super().smt2_encode(encoder)

    __len__ = None

    @classmethod
    def _operator(cls, smt2op, *args, returns=None):
        "Helper for implementing operators."
        try:
            if returns is None:
                returns = cls
            args = [cls(arg) for arg in args]
            value = make_value(Opcode, smt2op, *args)
            return returns(value)
        except TypeError:
            print(sys.exc_info())
            return NotImplemented

    def __eq__(self, arg):
        return self._operator('=', self, arg, returns=Bool)

    def __ne__(self, arg):
        return self._operator('distinct', self, arg, returns=Bool)

    def bvadd(self, arg):
        "Addition modulo len(self)."
        return self._operator('bvadd', self, arg)

class BitVecClass(type):
    "Metaclass used to generate classes for bit vectors of fixed size."
    _cache = {}
    def __new__(mcs, bits):
        # return class if it was already cached
        if bits in mcs._cache:
            return mcs._cache[bits]

        name = 'BitVec{}'.format(bits)
        nspc = {'__len__': lambda _: bits}
        cls = type(name, (BitVecBase,), nspc)

        mcs._cache[bits] = cls
        return cls

def bitvec(bits, value=None):
    """Returns bit vector of class BitVec{bits}.
       Intialized with {value} or fresh symbol is {value} is missing.
       Shortcut for BitVecClass(bits)(value)."""
    cls = BitVecClass(bits)
    return cls(value)
