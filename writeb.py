import random
import sys

argv = sys.argv
mode = argv[1] if len(argv) > 1 else 'def1'

K = int(argv[2]) if len(argv) > 2 else 16
R = int(argv[3]) if len(argv) > 3 else 256
Seed = argv[4] if len(argv) > 4 else 192797

if Seed == '-':
    import time
    Seed = time.time()
Seed = int(Seed)
random.seed(Seed)

atype = '(Array (_ BitVec 32) (_ BitVec 8))'
itype = '(_ BitVec 32)'
etype = '(_ BitVec 8)'
rnd = lambda: '#x{:08x}'.format(random.randrange(R))

print('; Seed = {}'.format(Seed))
print('(set-logic QF_AUFBV)')
print('(declare-fun A0 ()', atype, ')')

if mode == 'def1':
    print('(define-fun M0 ((.a', itype, '))', etype, '(select A0 .a))')
    for k in range(K):
        x = rnd()
        y = rnd()
        f = '(ite (= .a {}) (M{} {}) (M{} .a))'.format(x, k, y, k)
        print('(define-fun M{} ((.a {})) {} {})'.format(k + 1, itype, etype, f))
    x = rnd()
    y = rnd()
    print('(assert (distinct (M{} {}) (M{} {})))'.format(K, x, K, y))
elif mode == 'def2':
    print('(define-fun M0 ((.a', itype, '))', etype, '(select A0 .a))')
    for k in range(K):
        x = rnd()
        y = rnd()
        f = '(M{} (ite (= .a {}) {} .a))'.format(k, x, y)
        print('(define-fun M{} ((.a {})) {} {})'.format(k + 1, itype, etype, f))
    x = rnd()
    y = rnd()
    print('(assert (distinct (M{} {}) (M{} {})))'.format(K, x, K, y))
elif mode == 'def3':
    print('(define-fun M0 ((.a', itype, '))', etype, '(select A0 .a))')
    for k in range(K):
        x = rnd()
        y = rnd()
        print('(declare-fun V{} () {})'.format(k, etype))
        print('(assert (= V{} (M{} {})))'.format(k, k, y))
        f = '(ite (= .a {}) V{} (M{} .a))'.format(x, k, k)
        print('(define-fun M{} ((.a {})) {} {})'.format(k + 1, itype, etype, f))
    x = rnd()
    y = rnd()
    print('(assert (distinct (M{} {}) (M{} {})))'.format(K, x, K, y))
elif mode == 'let':
    print('(assert (let ((M0 A0))')
    for k in range(K):
        x = rnd()
        y = rnd()
        print('(let ((X{} (select M{} {})))'.format(k, k, y))
        print('(let ((M{} (store M{} {} X{})))'.format(k + 1, k, x, k))
    x = rnd()
    y = rnd()
    print('(let ((X{} (select M{} {})))'.format(K, K, x))
    print('(let ((Y{} (select M{} {})))'.format(K, K, y))
    print('(distinct X{} Y{})'.format(K, K))
    print(')' * (2 * K + 4))
elif mode == 'declet':
    for k in range(K + 1):
        print('(declare-fun ?X{} () {})'.format(k, etype))
    print('(assert (let ((M0 A0))')
    for k in range(K):
        x = rnd()
        y = rnd()
        print('(let ((X{} (select M{} {})))'.format(k, k, y))
        print('(let ((M{} (store M{} {} X{})))'.format(k + 1, k, x, k))
    x = rnd()
    y = rnd()
    print('(let ((X{} (select M{} {})))'.format(K, K, x))
    print('(let ((Y{} (select M{} {})))'.format(K, K, y))
    print('(and')
    print('(distinct X{} Y{})'.format(K, K))
    for k in range(K + 1):
        print('(= X{} ?X{})'.format(k, k))
    print(')' * (2 * K + 5))
elif mode == 'declet2':
    print('(declare-fun C0 () Bool)')
    for k in range(K + 1):
        print('(declare-fun ?X{} () {})'.format(k, etype))
    print('(assert (let ((M0 A0))')
    for k in range(K):
        x = rnd()
        y = rnd()
        print('(let ((X{} (select M{} {})))'.format(k, k, y))
        print('(let ((C{} (and C{} (= X{} ?X{}))))'.format(k + 1, k, k, k))
        print('(let ((M{} (store M{} {} X{})))'.format(k + 1, k, x, k))
    x = rnd()
    y = rnd()
    print('(let ((X{} (select M{} {})))'.format(K, K, x))
    print('(let ((Y{} (select M{} {})))'.format(K, K, y))
    print('(and C{} (distinct X{} Y{}))'.format(K, K, K))
    print(')' * (3 * K + 4))
else:
    assert False, "Invalid mode"


    
print('(check-sat)')
print('(exit)')
