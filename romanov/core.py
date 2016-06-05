"Core primitives of Romanov environment"

from abc import ABC, abstractmethod
from collections import OrderedDict

class Encodable(ABC):
    "Class dedicated for objects that can be translated to SMTLIB2"
    def __init__(self):
        pass

    @abstractmethod
    def smt2_encode(self, encoder):
        "Encodes objects in SMTLIB2"

class Opcode(Encodable):
    "Abstraction of result of SMTLIB2 operation"
    def __init__(self, smt2op, returns, *args):
        super().__init__()
        self.smt2op = smt2op
        self.returns = returns
        self.args = args

    def smt2_encode(self, encoder):
        args = [encoder.encode(arg) for arg in self.args]
        formula = '({} {})'.format(self.smt2op, ' '.join(args))
        return formula

FRESH = object()

class Symbolic(Encodable):
    "Abstract class for symbolic classes in Romanov"
    def __init__(self, value=FRESH):
        super().__init__()
        #pylint: disable=maybe-no-member
        if value is FRESH or self.is_literal(value):
            # handle fresh variables and literals
            self.value = value
        elif isinstance(value, self.__class__):
            # copy value from Symbolic to a new one
            self.value = value.value
        elif isinstance(value, Opcode):
            # ensure that Opcode returns a compatible type
            if isinstance(self, value.returns):
                raise TypeError('Opcode returns non-compatible class')
            self.value = value
        else:
            raise TypeError('Value is non-compatible')
        #pylint: enable=maybe-no-member

    @classmethod
    def is_literal(cls, _):
        "Checks if value is a literal. By default Symbolic has no literals"
        return False

    @abstractmethod
    def smt2_type(self):
        "Returns string with SMTLIB2 type"

    def smt2_encode(self, encoder):
        # Literals should be handled in subclass
        assert not self.is_literal(self.value)

        if self.value is FRESH:
            return encoder.declare(self, self.smt2_type())
        else:
            return encoder.encode(self.value)

class Bool(Symbolic):
    "Abstraction of symbolic boolean variable"
    def __init__(self, value=FRESH):
        super().__init__(value)

    @classmethod
    def is_literal(cls, value):
        return isinstance(value, bool)

    def smt2_type(self):
        return 'Bool'

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
            value = Opcode(smt2op, Bool, *args)
            return Bool(value)
        except TypeError:
            return NotImplemented

    def __eq__(self, arg):
        return self._operator('=', self, arg)

    def __ne__(self, arg):
        return self._operator('distinct', self, arg)

class Encoder:
    "Encodes Symbolics as SMTLIB2"
    def __init__(self):
        self._declares = OrderedDict()
        self._assumes = []

    def assume(self, root):
        """Add assume to the encoded formula.
        The argument root must be Bool."""

    def declare(self, ref, smt2type):
        """Creates a new fresh variable of type smt2type.
           Returns label as string."""

    def encode(self, value):
        """Encodes value as SMTLIB2.
           Value must be Encodable.
           Returns SMTLIB2 label as string."""

    def emit(self):
        "Translates assumptions to SMTLIB2 query. Returns (large) string."
