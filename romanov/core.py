"Core classes and functions of Romanov system"

class _Context:
    "Private class used to trace assumes, asserts and dumps."
    def __init__(self):
        pass

class Context:
    "Public wrapper class for _Context"
    def __init__(self):
        self._priv = _Context()
