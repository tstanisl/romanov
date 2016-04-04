from subprocess import Popen, PIPE, DEVNULL, TimeoutExpired
from time import time
import sys

players = {
    'stp' : ('stp',),
    'cvc4' : ('cvc4',),
    'btor' : ('boolector',),
    'btor2' : ('boolector2',),
    'z3' : ('z3',),
    'msat' : ('mathsat','-config=smtcomp2015_main.txt'),
    'yices' : ('yices-smt2',),
    'sono' : ('sonolar',),
}

for arg in sys.argv[1:]:
    for nick, cmd in players.items():
        cmdline = cmd + (arg,)
        tic = time()
        pipe = Popen(cmdline, stdout=PIPE, stderr=DEVNULL)
        try:
            ans, _ = pipe.communicate(timeout=10)
            ans = ans.decode().strip()
            if ans.startswith('unknown'):
                ans = 'unknown'
            if ans not in ('sat', 'unsat', 'unknown', 'timeout'):
                ans = 'failure'
            pipe = None
        except TimeoutExpired:
            ans = 'timeout'
        except:
            ans = 'failure'

        if pipe:
            pipe.kill()
            pipe.communicate()

        toc = time()
        print(arg, nick, ans, str(toc - tic))

