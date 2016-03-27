import romanov.core

class Solver:
    def __init__(self, *, logic = 'QF_AUFBV', has_model = True, options = {}):
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

class DumpSolver(Solver):
    def __init__(self, report_file):
        Solver.__init__(self, has_model = False)
        self._report_file = report_file
    def emit(self, smt):
        self._report_file.write(smt)
        self._report_file.write('\n')
    def recv(self):
        return 'unknown'
