"Core primitives of Romanov environment"

from abc import ABC, abstractmethod
from collections import OrderedDict

class Encodable(ABC):
    "Class dedicated for objects that can be translated to SMTLIB2"
    def __init__(self):
        pass

    @abstractmethod
    def encode(self, encoder):
        "Encodes objects in SMTLIB2"

class Opcode(Encodable):
    "Abstraction of result of SMTLIB2 operation"
    def __init__(self, smt2op, returns, *args):
        super().__init__()
        self.smt2op = smt2op
        self.returns = returns
        self.args = args

    def encode(self, encoder):
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
                raise TypeError('Opcode returns non-compalible class')
            self.value = value
        else:
            raise TypeError('Value is non-compatible')
        #pylint: enable=maybe-no-member

    @classmethod
    def is_literal(cls, _):
        "Checks if value is a literal. By default Symbolic has no literals"
        return False

    def encode(self, value):
        pass

class Encoder:
    "Encodes Symbolics as SMTLIB2"
    def __init__(self):
        self._declares = OrderedDict()
        self._assumes = []

    def assume(self, root):
        "Add assume to the encoded formula. The argument root must be Bool"

    def encode(self):
        "Runs encoding process. Returns string."
