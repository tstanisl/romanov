import romanov.core

class Solver:
    def __init__(self, logic = 'QF_AUFBV', has_model = True, options = {}):
        self._logic = logic
        self.has_model = has_model
        self._options = options

    def reset(self):
        for key, val in self._options:
            self.emit('(set-option :{} {})'.format(key, val))
        self.emit('(set-logic {})'.format(self._logic))
        
    def emit(self, smt):
        raise NotImplementedError

    def recv(self):
        raise NotImplementedError
