from cvc5.pythonic import *

if __name__ == "__main__":
    A, B, C = [Set(name, IntSort()) for name in "ABC"]

    # holds
    prove((A | B) & C == (A & C) | (B & C))

    # holds
    prove(IsSubset(EmptySet(IntSort()), A))

    # x must be 2.
    x = Int("x")
    solve(
        IsMember(
            x,
            (Singleton(IntVal(1)) | Singleton(IntVal(2)))
            & (Singleton(IntVal(2)) | Singleton(IntVal(3))),
        )
    )
