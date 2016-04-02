import random
import sys

argv = sys.argv
mode = argv[1] if len(argv) > 1 else 'def'

K = int(argv[2]) if len(argv) > 2 else 16
R = int(argv[3]) if len(argv) > 3 else 16
Seed = argv[4] if len(argv) > 4 else 192797

if Seed == '-':
    import time
    Seed = time.time()
Seed = int(Seed)
random.seed(Seed)

bits = 32
itype = '(_ BitVec 32)'
etype = '(_ BitVec {})'.format(bits)
atype = '(Array {} {})'.format(itype, etype)
rnd = lambda: '#x{:08x}'.format(random.randrange(R))
ops = ['bvadd', 'bvsub', 'bvor', 'bvnor', 'bvand', 'bvnand', 'bvxor']

print('; Seed = {}'.format(Seed))
print('(set-logic QF_AUFBV)')

if mode == 'def':
    for r in range(R):
        print('(declare-fun X{} () {})'.format(r, etype))
    for k in range(K):
        #x = 'X' + str(random.randrange(R + k))
        x = 'X' + str(R + k - 1)
        if k & 1:
            y = 'X' + str(random.randrange(R + k))
            #y = 'X' + str((R + k) // 2)
        else:
            y = '#x{:0{digits}x}'.format(random.randrange(2**bits), digits=bits//4)
        op = ops[random.randrange(len(ops))]
        print('(define-fun X{} () {} ({} {} {}))'.format(
              R + k, etype, op, x, y))
    print('(assert (= X{} X0))'.format(R + K - 1))
else:
    assert False, "Invalid mode"

print('(check-sat)')
print('(exit)')

