"SMTLIB2 Solvers used with Romanov package"

from abc import ABCMeta, abstractmethod
import subprocess
import threading

class Solver(metaclass=ABCMeta):
    "Abstract base class for SMT2 solvers"
    def __init__(self):
        pass

    @abstractmethod
    def reset(self):
        "Resets solver state to initial one"

    @abstractmethod
    def emit(self, smt2):
        "Process SMTLIB2 statement."

    @abstractmethod
    def recv(self):
        "Receives output produced by the solver"

class DumpSolver(Solver):
    "Dummy solver that prints SMT2 clauses to file. recv() returns 'unknown'"
    def __init__(self, report_file):
        super().__init__()
        self._rfile = report_file

    def reset(self):
        pass

    def emit(self, smt2):
        self._rfile.write(smt2)
        self._rfile.write('\n')

    def recv(self):
        self._rfile.flush()
        return 'unknown'

class PipeSolver(Solver):
    "Solver run in a new process. Communication via PIPEs."
    def __init__(self, args, env=None, timeout=None):
        super().__init__()
        self._args = args
        self._env = env or {}
        self._timeout = timeout
        self._pipe = None

    def _cleanup(self):
        "Clear internal pipe to external solver."
        if self._pipe:
            # Close stdin/stdout to avoid 'ResourceWarning: unclosed file'
            self._pipe.stdin.close()
            self._pipe.stdout.close()
            # terminate child process
            self._pipe.terminate()
            self._pipe = None

    def reset(self):
        self._cleanup()

        self._pipe = subprocess.Popen(self._args, env=self._env,
                                      bufsize=1, universal_newlines=True,
                                      stdin=subprocess.PIPE,
                                      stdout=subprocess.PIPE,
                                      stderr=subprocess.DEVNULL)

    def emit(self, smt):
        self._pipe.stdin.write(smt)
        self._pipe.stdin.write('\n')

    def recv(self):
        self._pipe.stdin.flush()
        ans = None
        def __func():
            "Worker function. Waits on stdout and saves result to {ans}."
            nonlocal ans
            ans = self._pipe.stdout.readline().strip()

        worker = threading.Thread(target=__func)
        worker.start()
        worker.join(self._timeout)

        if worker.is_alive():
            self._cleanup()
            worker.join()
            return 'timeout'

        return ans

    def __del__(self):
        self._cleanup()
