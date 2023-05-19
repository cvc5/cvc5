from cvc5.pythonic import *

if __name__ == "__main__":
    x, y, z = FPs("x y z", Float32())
    set_default_rounding_mode(RoundNearestTiesToEven())

    # FP addition is *not* commutative. This finds a counterexample.
    assert not is_tautology(fpEQ(x + y, y + x))

    # Without NaN or infinities, it is commutative. This proof succeeds.
    assert is_tautology(
        Implies(
            Not(Or(fpIsNaN(x), fpIsNaN(y), fpIsInf(x), fpIsInf(y))), fpEQ(x + y, y + x)
        )
    )

    pi = FPVal(+3.14, Float32())

    # FP addition is *not* associative in the range (-pi, pi).
    assert not is_tautology(
        Implies(
            And(x >= -pi, x <= pi, y >= -pi, y <= pi, z >= -pi, z <= pi),
            fpEQ((x + y) + z, x + (y + z)),
        )
    )
