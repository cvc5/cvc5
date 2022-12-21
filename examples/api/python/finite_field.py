###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test for cvc5's finite field solver.
#
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()
    slv.setOption("produce-models", "true")
    F = slv.mkFiniteFieldSort("5")
    a = slv.mkConst(F, "a")
    b = slv.mkConst(F, "b")

    inv = slv.mkTerm(
        Kind.EQUAL,
        slv.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
        slv.mkFiniteFieldElem("1", F),
    )
    aIsTwo = slv.mkTerm(
        Kind.EQUAL,
        a,
        slv.mkFiniteFieldElem("2", F),
    )
    # ab - 1 = 0
    slv.assertFormula(inv)
    # a = 2
    slv.assertFormula(aIsTwo)
    r = slv.checkSat()

    # should be SAT, with b = 2^(-1)
    assert r.isSat()
    print(slv.getValue(a).toPythonObj())
    assert slv.getValue(b).toPythonObj() == -2

    bIsTwo = slv.mkTerm(
        Kind.EQUAL,
        b,
        slv.mkFiniteFieldElem("2", F),
    )

    # b = 2
    slv.assertFormula(bIsTwo)
    r = slv.checkSat()

    # should be UNSAT, since 2*2 - 1 != 0
    assert not r.isSat()
