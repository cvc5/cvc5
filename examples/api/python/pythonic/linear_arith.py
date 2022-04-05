from cvc5.pythonic import *

slv = SolverFor('QF_LIRA')

x = Int('x')
y = Real('y')

slv += And(x >= 3 * y, x <= y, -2 < x)
slv.push()
print(slv.check(y-x <= 2/3))
slv.pop()
slv.push()
slv += y-x == 2/3
print(slv.check())
slv.pop()
