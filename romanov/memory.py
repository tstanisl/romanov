"Tracking memory states and operations"

from abc import abstractmethod
from romanov.core import Symbolic

class Memory(Symbolic):
    "Abstraction of memory state."
    def __init__(self, value):
        super().__init__(value)

    @abstractmethod
    def read(self, addr):
        "Reads one byte (BitVec8) from Memory."

    @abstractmethod
    def write(self, addr, data):
        "Returns new Memory after storing byte {data} at address {addr}/."

    @abstractmethod
    def copy(self, dst, src, size):
        """Implements C-style memmove({dst}, {src}, {size}).
           Return Memory object after operation"""

class SmtlibMemory(Memory):
    def __init__(self, value):
        valid_types = (type(None), Smtlib2Memory, Opcode)
        if not isinstance(value, valid_types):
            raise TypeError('value not compatible with SmtlibMemory')
        super().__init__(value)

    def read(self, addr):
        addr = bitvec(32, addr)
        value = make_value(Opcode, 'select', self, addr)
        return bitvec(8, value)

    def write(
