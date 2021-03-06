import re
import subprocess
import sys

_current = None

class Context:
    def __init__(self, args = None):
        if args == None:
            self._outfile = sys.stdout
            self._infile = None
        else:
            pipe = subprocess.Popen(args, stdin = subprocess.PIPE,
                stdout = subprocess.PIPE, universal_newlines = True,
                bufsize = 1)
            self._outfile = pipe.stdin
            self._infile = pipe.stdout
        self._ntmp = 0
        self._dumps = dict()
        self._outfile.write('(set-logic QF_BV)\n')

def make_current(ctx):
    global _current
    _current = ctx

def emit(smt):
        _current._outfile.write(smt)
        _current._outfile.write('\n')

def query(smt = None):
    if smt:
        emit(smt)
    _current._outfile.flush()
    if not _current._infile:
        return 'unknown'
    return _current._infile.readline().strip()

def newtmp(sort, value = None):
    ntmp = getattr(newtmp, 'ntmp', 0)
    name = 'T{}'.format(ntmp)
    if isinstance(sort, int):
        sort = '(_ BitVec {})'.format(sort)
    if value is None:
        emit('(declare-fun {} () {})'.format(name, sort))
    else:
        emit('(define-fun {} () {} {})'.format(name, sort, value))
    newtmp.ntmp = ntmp + 1
    return name

class BV:
    def __init__(self, bits, _value = None):
        assert isinstance(bits, int)
        assert bits > 0
        self._bits = bits
        self._str = newtmp(bits, _value)

    def _extend(self, exbits, exfunc):
        assert exbits >= 0
        if exbits == 0:
            return self
        formula = '((_ {} {}) {})'.format(exfunc, exbits, self)
        return BV(len(self) + exbits, formula)

    def signex(self, bits):
        return self._extend(bits - len(self), 'sign_extend')

    def zeroex(self, bits):
        return self._extend(bits - len(self), 'zero_extend')

    def __len__(self):
        return self._bits

    def __str__(self):
        return self._str

    def __eq__(a, b):
        assert isinstance(a, BV)
        assert isinstance(b, BV)
        assert len(a) == len(b)
        formula = '(bvcomp {} {})'.format(a, b)
        res = BV(1, formula)
        return res

class Int():
    def __init__(self, bits = 16, _value = None):
        self._bv = BV(bits, _value)

    def _from_int(val):
        assert isinstance(val, int)
        if val >= 0:
            bits = val.bit_length() + 1
            formula = '(_ bv{} {})'.format(val, bits)
        else:
            bits = (1 + val).bit_length() + 1
            formula = '(_ bv{} {})'.format(2 ** bits + val, bits)
        return Int(bits, formula)

    def __str__(self):
        return str(self._bv)

    def _cmp(a, b, smt2func):
        if isinstance(a, int):
            a = Int._from_int(a)
        if isinstance(b, int):
            b = Int._from_int(b)
        assert isinstance(a, Int)
        assert isinstance(b, Int)
        bits = max(len(a._bv), len(b._bv))
        a = a._bv.signex(bits)
        b = b._bv.signex(bits)
        formula = '({} {} {})'.format(smt2func, a, b)
        return Bool(formula)

    def __eq__(a, b):
        return Int._cmp(a, b, '=')
    def __ne__(a, b):
        return Int._cmp(a, b, 'distinct')
    def __gt__(a, b):
        return Int._cmp(a, b, 'bvsgt')
    def __ge__(a, b):
        return Int._cmp(a, b, 'bvsge')
    def __lt__(a, b):
        return Int._cmp(a, b, 'bvslt')
    def __le__(a, b):
        return Int._cmp(a, b, 'bvsle')

    def _op2(a, b, smt2func, bitsfunc):
        if isinstance(a, int):
            a = Int._from_int(a)
        if isinstance(b, int):
            b = Int._from_int(b)
        assert isinstance(a, Int)
        assert isinstance(b, Int)
        bits = bitsfunc(len(a._bv), len(b._bv))
        a = a._bv.signex(bits)
        b = b._bv.signex(bits)
        formula = '({} {} {})'.format(smt2func, a, b)
        return Int(bits, formula)
    def __add__(a, b):
        return Int._op2(a, b, 'bvadd', lambda a,b: max(a,b) + 1)
    def __radd__(a, b):
        return Int._op2(a, b, 'bvadd', lambda a,b: max(a, b) + 1)
    def __mul__(a, b):
        return Int._op2(a, b, 'bvmul', int.__add__)
    def __rmul__(a, b):
        return Int._op2(a, b, 'bvmul', int.__add__)

def Unsigned(bv):
        assert isinstance(bv, BV)
        bits = len(bv) + 1
        return Int(bits, bv.zeroex(bits))

def Signed(bv):
        assert isinstance(bv, BV)
        return Int(len(bv), bv)

class Bool():
    def __init__(self, _value = None):
        self._str = newtmp('Bool', _value)

    def _from_bool(val):
        assert isinstance(val, bool)
        return Bool('true' if val else 'false')

#    TODO: alternative implementation
#    def _op(fmt, *args):
#        args = (Bool._toBool(arg) for arg in *args)
#        formula = fmt.format(*args)
#        return Bool(formula)

    def _op2(a, b, smt2func):
        if isinstance(a, bool):
            a = Bool._from_bool(a)
        if isinstance(b, bool):
            b = Bool._from_bool(b)
        assert isinstance(a, Bool)
        assert isinstance(b, Bool)
        formula = '({} {} {})'.format(smt2func, a, b)
        return Bool(formula)

    def __eq__(a, b):
        return Bool._op2(a, b, '=')
    def __ne__(a, b):
        return Bool._op2(a, b, 'dictinct')
    def __and__(a, b):
        return Bool._op2(a, b, 'and')
    def __rand__(a, b):
        return Bool._op2(a, b, 'and')
    def __or__(a, b):
        return Bool._op2(a, b, 'or')
    def __ror__(a, b):
        return Bool._op2(a, b, 'or')
    def __xor__(a, b):
        return Bool._op2(a, b, 'xor')
    def __rxor__(a, b):
        return Bool._op2(a, b, 'xor')
    def __rshift__(a, b):
        return Bool._op2(a, b, '=>')
    def __rrshift__(a, b):
        return Bool._op2(b, a, '=>')
    def __inv__(a):
        assert isinstance(a, Bool)
        return Bool('(not {})'.format(a))

    def __str__(self):
        return str(self._str)

_dumps = dict()

def Dump(value, name):
    if '|' in name:
        raise AttributeError('| is not allowed in Dump name')
    if name in _dumps:
        raise KeyError('name already used')
    _dumps[name] = value

def Assert(v):
    assert isinstance(v, Bool)
    emit('(assert (not {}))'.format(v))
    ans = query('(check-sat)')
    if ans == 'unsat':
        return True
    for k,v in _dumps.items():
        ans = query('(get-value ({}))'.format(v))
        rexp = r'\(\({} (.*)\)\)'.format(v)
        match = re.fullmatch(rexp, ans)
        if match:
            print(k, ':', match.group(1))
        else:
            print('Syntax error:', ans)

        #match = rexp.
        #ans = [x for x in re.split('[()\s]', ans) if x]
        #print(k, ':', ans[1])
    return True

def Assume(v):
    assert isinstance(v, Bool)
    emit('(assert {})'.format(v))

def test0():
    a = BV(4)
    b = BV(4)
    c = (a == b)
    d = Int(4)
    e = Signed(c)
    f = Unsigned(a)
    g = Int(3)
    h = (d == g)
    i = (g == 2)
    j = (-4 < g)
    k = Bool()
    l = (k == j)
    m = (j == False)
    x = Int()
    y = Int()
    u = (x + 3 == y)

def test1():
    x = Int()
    y = Int()
    Dump(x, 'x')
    Dump(y, 'y')
    Assume(x > 1)
    Assume(y > 1)
    Assert(x + y > 4)

if __name__ == "__main__":
    #ctx = Context()
    #ctx = Context(['z3', '-smt2', '-in'])
    #ctx = Context(['boolector2', '-i', '-m'])
    ctx = Context(['yices-smt2'])
    #ctx = Context(['cvc4', '--lang', 'smt2', '-m'])
    #ctx = Context(['stp', '--SMTLIB2'])
    make_current(ctx)
    test1()
