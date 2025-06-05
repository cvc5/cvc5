###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir, Anjiang-Wei
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# An example of solving floating-point problems with cvc5's Python API.
#
# This example shows to create floating-point types, variables and expressions,
# and how to create rounding mode constants by solving toy problems. The
# example also shows making special values (such as NaN and +oo) and converting
# an IEEE 754-2008 bit-vector to a floating-point number.
##
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
