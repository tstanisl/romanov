from romanov import *

if __name__ == '__main__':
    encoder = Encoder()

    a = bitvec(8)
    b = bitvec(8)

    encoder.assume(a == b)

    d = Bool()
    c = a.ite(d, a, a)

    encoder.assume(c != a)

    A = bitvec(8,1)
    B = bitvec(8,25)
    C = B.bvadd(A)
    encoder.assume(C == 26)

    print(encoder.encode())
