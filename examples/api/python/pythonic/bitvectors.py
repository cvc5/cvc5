from cvc5.pythonic import *

if __name__ == '__main__':
    # The following example has been adapted from the book A Hacker's Delight
    # by Henry S. Warren.
    #
    # Given a variable x that can only have two values, a or b. We want to
    # assign to x a value other than the current one. The straightforward code
    # to do that is:
    #
    # (0) if (x == a ) x = b;
    #     else x = a;
    #
    # Two more efficient yet equivalent methods are:
    #
    # (1) x = a xor b xor x;
    #
    # (2) x = a + b - x;
    #
    # We will use cvc5 to prove that the three pieces of code above are all
    # equivalent by encoding the problem in the bit-vector theory.

    x, a, b = BitVecs('x a b', 32)
    x_is_a_or_b = Or(x == a, x == b)

    # new_x0 set per (0)
    new_x0 = If(x == a, b, a)
    # new_x1 set per (1)
    new_x1 = a ^ b ^ x
    # new_x2 set per (2)
    new_x2 = a + b - x

    prove(Implies(x_is_a_or_b, new_x0 == new_x1))

    prove(Implies(x_is_a_or_b, new_x0 == new_x2))
