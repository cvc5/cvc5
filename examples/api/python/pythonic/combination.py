from cvc5.pythonic import *

if __name__ == "__main__":

    U = DeclareSort("U")
    x, y = Consts("x y", U)

    f = Function("f", U, IntSort())
    p = Function("p", IntSort(), BoolSort())

    assumptions = [f(x) >= 0, f(y) >= 0, f(x) + f(y) <= 1, Not(p(0)), p(f(y))]

    prove(Implies(And(assumptions), x != y))

    s = Solver()
    s.add(assumptions)
    assert sat == s.check()
    m = s.model()

    def print_val(t):
        print("{}: {}".format(t, m[t]))

    # print the of some terms
    print_val(f(x))
    print_val(f(y))
    print_val(f(x) + f(y))
    print_val(p(0))
    print_val(p(f(y)))

    # print value of *all* terms
    def print_all_subterms(t):
        print_val(t)
        for c in t.children():
            print_all_subterms(c)
    print_all_subterms(And(assumptions))
