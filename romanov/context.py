"Core classes and functions of Romanov system"

class Context:
    "Class used to trace assumes, asserts and dumps."
    def __init__(self):
        pass

def current():
    "Returns active context. May return None."
    return getattr(current, "context", None)

def make_current(new):
    "Sets new active context. Returns previous one."
    if not isinstance(new, (type(None), Context)):
        raise TypeError('Argument of make_current() must be Context or None')

    old = current()
    current.context = new
    return old
