from cvc5.pythonic import *

if __name__ == '__main__':
    x = BitVec('x', 32)

    # Consider the bits of x: 01234567
    # (we assume 8 bits to make the visualization simple)
    #
    # If      1234567
    # equals  0123456
    #
    # then    0 == 7 (by induction over the bits)

    prove(Implies(Extract(31, 1, x) == Extract(30, 0, x),
                  Extract(31, 31, x) == Extract(0, 0, x)))
