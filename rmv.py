def emit(smt):
    print(smt)

class BV:
    _nBVs = 0

    def __init__(self, bits, _value = None):
        assert isinstance(bits, int)
        assert bits > 0
        self.bits = bits
        self._str = 'T{}'.format(BV._nBVs)
        BV._nBVs += 1
        bvstr = '(_ BitVec {})'.format(bits)
        if _value is None:
            emit('(declare-fun {} () {})'.format(self, bvstr))
        else:
            emit('(define-fun {} () {} {})'.format(self, bvstr, _value))


    def __str__(self):
        return self._str

    def __eq__(a, b):
        assert isinstance(a, BV)
        assert isinstance(b, BV)
        assert a.bits == b.bits
        formula = '(bvcomp {} {})'.format(a, b)
        res = BV(1, formula)
        return res

class Int():
    def __init__(self, bits = 16):
        self.bv = BV(bits)

    def __str__(self):
        return str(self.bv)

class Unsigned(Int):
    def __init__(self, bv):
        assert isinstance(bv, BV)
        Int.__init__(self, bv.bits + 1)
        emit('(assert (= {} ((_ zero_extend 1) {})))'.format(self, bv))

class Signed(Int):
    def __init__(self, bv):
        assert isinstance(bv, BV)
        Int.__init__(self, bv.bits)
        emit('(assert (= {} {}))'.format(self, bv))

def main():
    a = BV(4)
    b = BV(4)
    c = (a == b)
    d = Int(4)
    e = Signed(c)
    f = Unsigned(a)

if __name__ == "__main__":
	main()
