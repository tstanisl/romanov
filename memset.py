import random
import sys
import time

argv = sys.argv
mode = argv[1] if len(argv) > 1 else 'def'

K = int(argv[2]) if len(argv) > 2 else 16
ibits = int(argv[3]) if len(argv) > 3 else 16
sbits = int(argv[4]) if len(argv) > 4 else 16
Seed = argv[5] if len(argv) > 5 else time.time()
Seed = int(Seed)

assert 0 < sbits <= ibits

random.seed(Seed)

# generates K operations of types 
# memset(var/const, read(x)/const, var/const)
#K = (K + 7) & ~7
#V = K // 4
V = (K + 3) // 4

itype = '(_ BitVec {})'.format(ibits)
stype = '(_ BitVec {})'.format(sbits)
etype = '(_ BitVec 8)'
atype = '(Array {} {})'.format(itype, etype)
rnd = random.randrange

rndb = lambda: '(_ bv{} 8)'.format(rnd(256))
rndi = lambda: '(_ bv{} {})'.format(rnd(2 ** ibits), ibits)
rnds = lambda: '(_ bv{} {})'.format(rnd(2 ** sbits), sbits)

s2i = lambda x: x
if ibits > sbits:
    s2i = lambda x: '((_ zero_extend {}) {})'.format(ibits - sbits, x)

print('; Seed = {}'.format(Seed))
print('(set-logic QF_AUFBV)')
print('(declare-fun A0 ()', atype, ')')

for v in range(V):
    print('(declare-fun P{} () {})'.format(v, itype))
    print('(declare-fun S{} () {})'.format(v, stype))

if mode == 'def1':
    print('(define-fun M0 ((.a {})) {} (select A0 .a))'.format(itype, etype))
    for k in range(K):
        m = rnd(8)
        dst = rndi() if m & 1 else 'P{}'.format(rnd(V))
        val = rndb() if m & 2 else '(M{} {})'.format(k, rndi())
        size = rnds() if m & 4 else 'S{}'.format(rnd(V))
        print('(define-fun M{} ((.a {})) {}'.format(k + 1, itype, etype))
        print('    (let ((.off (bvsub .a {})))'.format(dst))
        print('    (ite (bvult .off {}) {} (M{} .a))))'.format(s2i(size), val, k))
    x = '(M{} {})'.format(K, rndi())
    y = '(M{} {})'.format(K, rndi())
    print('(assert (= {} {}))'.format(x, y))
    x = '(M{} {})'.format(K, rndi())
    y = '(M{} {})'.format(K, rndi())
    print('(assert (distinct {} {}))'.format(x, y))
elif mode == 'def2':
    print('(define-fun M0 ((.a {})) {} (select A0 .a))'.format(itype, etype))
    for k in range(K):
        m = rnd(8)
        dst = rndi() if m & 1 else 'P{}'.format(rnd(V))
        val = rndb() if m & 2 else '(M{} {})'.format(k, rndi())
        size = rnds() if m & 4 else 'S{}'.format(rnd(V))
        print('(define-fun M{} ((.a {})) {}'.format(k + 1, itype, etype))
        print('    (let ((.c0 (bvule {} .a)))'.format(dst))
        print('    (let ((.h (bvadd {} {})))'.format(dst, s2i(size)))
        print('    (let ((.c1 (bvult .a .h)))')
        print('    (ite (and .c0 .c1) {} (M{} .a))))))'.format(val, k))
    x = '(M{} {})'.format(K, rndi())
    y = '(M{} {})'.format(K, rndi())
    print('(assert (= {} {}))'.format(x, y))
    x = '(M{} {})'.format(K, rndi())
    y = '(M{} {})'.format(K, rndi())
    print('(assert (distinct {} {}))'.format(x, y))
elif mode == 'def3':
    print('(define-fun M0 ((.a {})) {} (select A0 .a))'.format(itype, etype))
    for k in range(K):
        m = rnd(8)
        dst = rndi() if m & 1 else 'P{}'.format(rnd(V))
        val = rndb() if m & 2 else '(M{} {})'.format(k, rndi())
        size = rnds() if m & 4 else 'S{}'.format(rnd(V))
        print('(declare-fun V{} () {})'.format(k, etype))
        print('(assert (= V{} {}))'.format(k, val))
        print('(define-fun M{} ((.a {})) {}'.format(k + 1, itype, etype))
        print('    (let ((.off (bvsub .a {})))'.format(dst))
        print('    (ite (bvult .off {}) V{} (M{} .a))))'.format(s2i(size), k, k))
    x = '(M{} {})'.format(K, rndi())
    y = '(M{} {})'.format(K, rndi())
    print('(assert (= {} {}))'.format(x, y))
    x = '(M{} {})'.format(K, rndi())
    y = '(M{} {})'.format(K, rndi())
    print('(assert (distinct {} {}))'.format(x, y))
elif mode == 'unroll':
    print('(declare-fun M0 () {})'.format(atype))
    print('(assert (= M0 A0))')
    for k in range(K):
        m = rnd(8)
        dst = rndi() if m & 1 else 'P{}'.format(rnd(V))
        val = rndb() if m & 2 else '(select M{} {})'.format(k, rndi())
        size = rnds() if m & 4 else 'S{}'.format(rnd(V))
        print('(declare-fun M{} () {})'.format(k + 1, atype))
        print('(assert')
        print('(let ((S {}))'.format(size))
        print('(let ((V {}))'.format(val))
        print('(let ((H0 M{}))'.format(k))
        for i in range(2**sbits):
            bi = '(_ bv{} {})'.format(i, sbits)
            pos = '(bvadd {} (_ bv{} {}))'.format(dst, i, ibits)
            print('(let ((H{} (ite (bvult {} S) (store H{} {} V) H{})))'.format(
                i + 1, bi, i, pos, i))
        print('(= M{} H{})'.format(k + 1, 2**sbits))
        print(')'*(2**sbits + 4))
    x = '(select M{} {})'.format(K, rndi())
    y = '(select M{} {})'.format(K, rndi())
    print('(assert (= {} {}))'.format(x, y))
    x = '(select M{} {})'.format(K, rndi())
    y = '(select M{} {})'.format(K, rndi())
    print('(assert (distinct {} {}))'.format(x, y))
elif mode == 'inst':
    for k in range(K + 1):
        print('(declare-fun M{} () {})'.format(k, atype))
    memsets = []
    C = 0
    def emit(p):
        global C
        K = len(memsets)
        for k, memset in enumerate(memsets, start=1):
            dst, val, size = memset
            L = '(select M{} {})'.format(k, p)
            R = '(ite (bvult (bvsub {} {}) {}) {} (select M{} {}))'.format(
                p, dst, s2i(size), val, k - 1, p)
            print('(let ((C{} (and C{} (= {} {}))))'.format(C + 1, C, L, R))
            C += 1

    print('(assert')
    print('(let ((C0 true))')
    for k in range(K):
        m = rnd(8)
        dst = rndi() if m & 1 else 'P{}'.format(rnd(V))
        val = rndb() if m & 2 else rndi()
        size = rnds() if m & 4 else 'S{}'.format(rnd(V))
        if m & 2 == 0:
            emit(val)
            val = '(select M{} {})'.format(k, val)
        print('(let ((V{} {}))'.format(k, val))
        val = 'V{}'.format(k)
        memset = (dst, val, size)
        memsets.append(memset)

    X = [rndi(), rndi(), rndi(), rndi()]
    for i, x in enumerate(X):
        emit(x)
        print('(let ((X{} (select M{} {})))'.format(i, K, x))

    print('(and C{} (= X0 X1) (distinct X2 X3))'.format(C))
    print(')' * (K + C + 6))
else:
    assert False, "Invalid mode"

print('(check-sat)')
print('(exit)')
