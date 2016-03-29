'SMTLIB2 Solvers used with RMV package'

import subprocess

class Solver:
    "Abstract base class for SMT2 solvers"
    def __init__(self, *, logic='QF_AUFBV', has_model=True, options={}):
        self._logic = logic
        self.has_model = has_model
        self._options = options

    def reset(self):
        "Resets solver to initial state."
        for key, val in self._options.items():
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
    def __init__(self, report_file, **kwargs):
        Solver.__init__(self, has_model=False, **kwargs)
        self._report_file = report_file
    def emit(self, smt):
        self._report_file.write(smt)
        self._report_file.write('\n')
    def recv(self):
        return 'unknown'

class PipeSolver(Solver):
    "Solver that spawns a new process and communicates via pipe."
    def __init__(self, args, *, env={}, **kwargs):
        Solver.__init__(self, **kwargs)
        self._args = args
        self._env = env
        self._pipe = None

    def reset(self):
        if self._pipe is not None:
            self._pipe.terminate()

        self._pipe = subprocess.Popen(self._args, env=self._env,
                                      bufsize=1, universal_newlines=True,
                                      stdin=subprocess.PIPE,
                                      stdout=subprocess.PIPE,
                                      stderr=subprocess.DEVNULL)

        Solver.reset(self)

    def emit(self, smt):
        self._pipe.stdin.write(smt)
        self._pipe.stdin.write('\n')

    def recv(self):
        self._pipe.stdin.flush()
        return self._pipe.stdout.readline().strip()
