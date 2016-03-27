'SMTLIB2 Solvers used with RMV package'

class Solver:
    "Abstract base class for SMT2 solvers"
    def __init__(self, *, logic='QF_AUFBV', has_model=True, options={}):
        self._logic = logic
        self.has_model = has_model
        self._options = options

    def reset(self):
        "Resets solver to initial state."
        for key, val in self._options:
            self.emit('(set-option :{} {})'.format(key, val))
        self.emit('(set-logic {})'.format(self._logic))

    def emit(self, smt):
        "Emits SMT2 expression."
        raise NotImplementedError

    def recv(self):
        "Query solver for satisfiability or model."
        raise NotImplementedError

class DumpSolver(Solver):
    "Dummy solver that prints SMT2 clauses to file. recv() returns 'unknown'"
    def __init__(self, report_file):
        Solver.__init__(self, has_model=False)
        self._report_file = report_file
    def emit(self, smt):
        self._report_file.write(smt)
        self._report_file.write('\n')
    def recv(self):
        return 'unknown'
