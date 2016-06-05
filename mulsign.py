import random
import sys
import time

try:
    mode = sys.argv[1]
    ibits = int(sys.argv[2])
    obits = int(sys.argv[3])

    assert obits >= 2 * ibits

    seed = sys.argv[4] if len(sys.argv) >= 5 else time.time()
    seed = int(seed)
except:
    print("Unexpected error:", sys.exc_info()[1])
    print('Usage:\n\t', sys.argv[0], 'mode ibits obits [seed]')
    sys.exit(-1)

random.seed(seed)
rnd = random.randrange

print('; seed = ', seed)
print('(set-logic QF_AUFBV)')

for i in range(10):
    R = rnd(1 << (2 * ibits))

    if mode == 'bounds':
        print('(declare-fun A{} () (_ BitVec {}))'.format(i, obits))
        print('(declare-fun B{} () (_ BitVec {}))'.format(i, obits))
        limit = 1 << (ibits - 1)
        L = 1 << obits
        print('(assert (bvslt A{} (_ bv{} {})))'.format(i, limit, obits))
        print('(assert (bvsge A{} (_ bv{} {})))'.format(i, L - limit, obits))
        print('(assert (bvslt B{} (_ bv{} {})))'.format(i, limit, obits))
        print('(assert (bvsge B{} (_ bv{} {})))'.format(i, L - limit, obits))
        print('(assert (= (bvmul A{} B{}) (_ bv{} {})))'.format(i, i, R, obits))
    elif mode == 'extend':
        print('(declare-fun A{} () (_ BitVec {}))'.format(i, ibits))
        print('(declare-fun B{} () (_ BitVec {}))'.format(i, ibits))
        print('(assert')
        print('(let ((a ((_ sign_extend {}) A{})))'.format(obits - ibits, i))
        print('(let ((b ((_ sign_extend {}) B{})))'.format(obits - ibits, i))
        print('(= (bvmul a b) (_ bv{} {}))'.format(R, obits))
        print(')))')
    else:
        assert False, "Invalid mode"

print('(check-sat)')
print('(exit)')
    

