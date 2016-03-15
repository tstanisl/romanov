def emit(smt):
    print(smt)

class BV:
    _nBVs = 0

    def __init__(self, bits, _value = None):
        assert isinstance(bits, int)
        assert bits > 0
        self._bits = bits
        self._str = 'T{}'.format(BV._nBVs)
        BV._nBVs += 1
        tstr = '(_ BitVec {})'.format(bits)
        if _value is None:
            emit('(declare-fun {} () {})'.format(self, tstr))
        else:
            emit('(define-fun {} () {} {})'.format(self, tstr, _value))

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
            bits = val.bit_length()
            formula = '(_ bv{} {})'.format(2 ** bits + val, bits)
        return Int(bits, formula)

    def __str__(self):
        return str(self._bv)

    def __eq__(a, b):
        if isinstance(a, int):
            a = Int._from_int(a)
        if isinstance(b, int):
            b = Int._from_int(b)
        assert isinstance(a, Int)
        assert isinstance(b, Int)
        bits = max(len(a._bv), len(b._bv))
        a = a._bv.signex(bits)
        b = b._bv.signex(bits)
        return a == b

class Unsigned(Int):
    def __init__(self, bv):
        assert isinstance(bv, BV)
        bits = len(bv) + 1
        Int.__init__(self, bits, bv.zeroex(bits))

class Signed(Int):
    def __init__(self, bv):
        assert isinstance(bv, BV)
        Int.__init__(self, len(bv), bv)

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
    j = (g == -342)

if __name__ == "__main__":
	main()
