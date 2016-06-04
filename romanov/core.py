"Core primitives of Romanov environment"

from abc import ABC, abstractmethod

class Encodable(ABC):
    "Class dedicated for objects that can be translated to SMTLIB2"
    def __init__(self):
        pass

    @abstractmethod
    def encode(self, encoder):
        "Encodes objects in SMTLIB2"
