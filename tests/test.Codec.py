from romanov import *
from romanov.solver import *
from romanov.core import Symbolic
import sys

def dump_vars(vardict, codec):
    for key, val in vardict.items():
        if isinstance(val, Symbolic):
            label = val.smt2_encode(codec)
            value = val.smt2_decode(codec)

            print(key, '(', label, ')', value)

if __name__ == '__main__':
    args = ('z3', '-in', '-smt2')
    solver = PipeSolver(args)
    #solver = DumpSolver(sys.stdout)
    codec = Codec(solver)

    x = Bool()
    y = Bool()

    codec.assume(x == y)

    ans = codec.solve()
    print(ans)

    dump_vars(vars(), codec)
