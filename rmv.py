def emit(smt):
    print(smt)

def _toBV(a):
    if isinstance(a, BV):
        return a
    elif isinstance(a, int):
        return Int(a)
    else:
        raise TypeError('Cannot convert to BV (bit vector)')

class BV:
    _nBVs = 0
    def __init__(self, bits):
        assert isinstance(bits, int)
        assert bits > 0
        BV.bits = bits
        BV._str = 'T{}'.format(BV._nBVs)
        BV._nBVs += 1
        emit('(declare-fun {} () (_ BitVec {}))'.format(self, bits))

    def __str__(self):
        return self._str

    def __eq__(a, b):
        b = _toBV(b)
        bits = max(a.bits, b.bits)
        res = BV(1)
        emit('(assert (= {} (bvcomp {} {})))'.format(res, a, b))
        return res

class Int(BV):
    def __init__(self, value = None, bits = 16):
        BV.__init__(self, bits)

def main():
    a = BV(4)
    b = BV(4)
    c = (a == b)

if __name__ == "__main__":
	main()
