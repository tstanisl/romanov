import random
import sys
import time

try:
    mode = sys.argv[1]
    ibits = int(sys.argv[2])
    obits = int(sys.argv[3])

    assert obits >= 2 * ibits

    seed = argv[4] if len(sys.argv) >= 5 else time.time()
    seed = int(seed)
except:
    print("Unexpected error:", sys.exc_info()[1])
    print('Usage:\n\t', sys.argv[0], 'mode ibits obits [seed]')
    sys.exit(-1)

random.seed(seed)
rnd = random.randrange

R = rnd(1 << (2 * ibits))

print('; seed = ', seed)
if mode == 'bounds':
    print('(declare-fun A () (_ BitVec {}))'.format(obits))
    print('(declare-fun B () (_ BitVec {}))'.format(obits))
    print('(assert (bvult A (_ bv{} {})))'.format(1 << ibits, obits))
    print('(assert (bvult B (_ bv{} {})))'.format(1 << ibits, obits))
    print('(assert (= (bvmul A B) (_ bv{} {})))'.format(R, obits))
else:
    assert False, "Invalid mode"

print('(check-sat)')
print('(exit)')
    
