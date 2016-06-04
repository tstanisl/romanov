"Core primitives of Romanov environment"

from abc import ABC, abstractmethod

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
