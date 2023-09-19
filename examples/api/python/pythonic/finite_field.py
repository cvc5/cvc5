from cvc5.pythonic import *

if __name__ == '__main__':
    F = FiniteFieldSort(5)
    a, b = FiniteFieldElems("a b", F)

    solve(a * b == 1, a == 2)
    # a = 2, b = -2 (or 3) is a solution.

    solve(a * b == 1, a == 2, b == 2)
    # no solution
