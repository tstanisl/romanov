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
    a = rnd(1 << ibits)
    b = rnd(1 << ibits)
    c = rnd(1 << ibits)

    if mode == 'bounds':
        print('(declare-fun A{} () (_ BitVec {}))'.format(i, obits))
        print('(declare-fun B{} () (_ BitVec {}))'.format(i, obits))
        limit = 1 << (ibits - 1)
        L = 1 << obits
        print('(assert (bvslt A{} (_ bv{} {})))'.format(i, limit, obits))
        print('(assert (bvsge A{} (_ bv{} {})))'.format(i, L - limit, obits))
        print('(assert (bvslt B{} (_ bv{} {})))'.format(i, limit, obits))
        print('(assert (bvsge B{} (_ bv{} {})))'.format(i, L - limit, obits))
        print('(assert')
        #print('(let ((a A{i}))'.format(i))
        print('(let ((a (_ bv{} {})))'.format(a, obits))
        print('(let ((b B{}))'.format(i))
        print('(let ((c (_ bv{c} {obits})))'.format(**vars()))
        print('(let ((L (bvmul a (bvadd b c))))')
        print('(let ((R (bvadd (bvmul a b) (bvmul a c))))')
        print('(distinct L R)')
#        print('(let ((L (bvmul A{i} (bvadd B{i} C))))'.format(**vars()))
#        print('(let ((R (bvadd (bvmul A{i} B{i}) (bvmul A{i} C))))'.format(**vars()))
#        print('(distinct L R)')
        print('))))))')
    elif mode == 'extend':
        print('(declare-fun A{} () (_ BitVec {}))'.format(i, ibits))
        print('(declare-fun B{} () (_ BitVec {}))'.format(i, ibits))
        print('(assert')
        #print('(let ((a ((_ sign_extend {}) A{})))'.format(obits - ibits, i))
        print('(let ((a (_ bv{} {})))'.format(a, obits))
        print('(let ((b ((_ sign_extend {}) B{})))'.format(obits - ibits, i))
        print('(let ((c (_ bv{} {})))'.format(c, obits))
        print('(let ((L (bvmul a (bvadd b c))))')
        print('(let ((R (bvadd (bvmul a b) (bvmul a c))))')
        print('(distinct L R)')
        print('))))))')
    else:
        assert False, "Invalid mode"

print('(check-sat)')
print('(exit)')

