from cvc5.pythonic import *

if __name__ == '__main__':

    # Let's introduce some variables
    x, y = Reals('x y')
    a, b = Ints('a b')

    # We will confirm that
    #  * 0 < x
    #  * 0 < y
    #  * x + y < 1
    #  * x <= y
    # are satisfiable
    solve(0 < x, 0 < y, x + y < 1, x <= y)

    # If we get the model (the satisfying assignment) explicitly, we can
    # evaluate terms under it.
    s = Solver()
    s.add(0 < x, 0 < y, x + y < 1, x <= y)
    assert sat == s.check()
    m = s.model()

    print('x:', m[x])
    print('y:', m[y])
    print('x - y:', m[x - y])

    # We can also get these values in other forms:
    print('string x:', str(m[x]))
    print('decimal x:', m[x].as_decimal(4))
    print('fraction x:', m[x].as_fraction())
    print('float x:', float(m[x].as_fraction()))

    # The above constraints are *UNSAT* for integer variables.
    # This reports "no solution"
    solve(0 < a, 0 < b, a + b < 1, a <= b)



