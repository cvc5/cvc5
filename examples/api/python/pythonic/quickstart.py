from cvc5.pythonic import *

if __name__ == '__main__':

    # Let's introduce some variables
    #! [docs-pythonic-quickstart-1 start]
    x, y = Reals('x y')
    a, b = Ints('a b')
    #! [docs-pythonic-quickstart-1 end]

    # We will confirm that
    #  * 0 < x
    #  * 0 < y
    #  * x + y < 1
    #  * x <= y
    # are satisfiable
    #! [docs-pythonic-quickstart-2 start]
    solve(0 < x, 0 < y, x + y < 1, x <= y)
    #! [docs-pythonic-quickstart-2 end]

    # If we get the model (the satisfying assignment) explicitly, we can
    # evaluate terms under it.
    #! [docs-pythonic-quickstart-3 start]
    s = Solver()
    s.add(0 < x, 0 < y, x + y < 1, x <= y)
    assert sat == s.check()
    m = s.model()
    #! [docs-pythonic-quickstart-3 end]

    #! [docs-pythonic-quickstart-4 start]
    print('x:', m[x])
    print('y:', m[y])
    print('x - y:', m[x - y])
    #! [docs-pythonic-quickstart-4 end]

    # We can also get these values in other forms:
    #! [docs-pythonic-quickstart-5 start]
    print('string x:', str(m[x]))
    print('decimal x:', m[x].as_decimal(4))
    print('fraction x:', m[x].as_fraction())
    print('float x:', float(m[x].as_fraction()))
    #! [docs-pythonic-quickstart-5 end]

    # The above constraints are *UNSAT* for integer variables.
    # This reports "no solution"
    #! [docs-pythonic-quickstart-6 start]
    solve(0 < a, 0 < b, a + b < 1, a <= b)
    #! [docs-pythonic-quickstart-6 end]



