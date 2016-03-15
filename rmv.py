def emit(smt):
    print(smt)

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

    def __str__(self):
        return str(self._str)

def main():
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

if __name__ == "__main__":
	main()
