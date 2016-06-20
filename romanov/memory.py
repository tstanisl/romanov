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
