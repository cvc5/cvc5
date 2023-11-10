from cvc5.pythonic import *

if __name__ == '__main__':
    F = FiniteFieldSort(5)
    a, b = FiniteFieldElems("a b", F)
    s = Solver()

    # a = 2, b = -2 (or 3) is a solution.
    r = s.check(a * b == 1, a == 2)
    assert r == sat
    print(s.model()[a])
    assert s.model()[b] == -2

    # no solution
    r = s.check(a * b == 1, a == 2, b == 2)
    assert r == unsat
