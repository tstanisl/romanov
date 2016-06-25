from romanov import *

if __name__ == '__main__':
    encoder = Encoder()
    a = Bool()
    b = Bool()
    c = a == b
    d = a == b
    #encoder.assume(c)
    encoder.assume(d)
    a = b >> True
    encoder.assume(a)
    print(encoder.encode())
  
    #help(c.smt2_encode)
