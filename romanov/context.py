"Core classes and functions of Romanov system"

class _Context:
    "Private class used to trace assumes, asserts and dumps."
    def __init__(self):
        pass

class Context:
    "Public wrapper class for _Context"
    def __init__(self):
        self._priv = _Context()

def current():
    "Returns active context. May return None."
    return getattr(current, "context", None)

def make_current(new):
    "Sets new active context. Returns previous one."
    if not(isinstance(new, Context) or new is None):
        raise TypeError('Argument of make_current() must be Context or None')

    old = current()
    current.context = new
    return old


