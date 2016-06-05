from romanov import *

if __name__ == '__main__':
    encoder = Encoder()
    a = Bool()
    b = Bool()
    c = a == b
    smt2 = encoder.encode(c)
    print(smt2)
