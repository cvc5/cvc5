from cvc5.pythonic import *

if __name__ == '__main__':
    x, y = Reals("x y")
    solve(x > Pi(),
            x < 2 * Pi(),
            y ** 2 < Sine(x))
