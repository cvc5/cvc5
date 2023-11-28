###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
from cvc5 import Sort, Term, Kind


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_basic_finite_field(solver):
    solver.setOption("produce-models", "true")
    F = solver.mkFiniteFieldSort(5)
    a = solver.mkConst(F, "a")
    b = solver.mkConst(F, "b")
    assert 5 == F.getFiniteFieldSize()

    inv = solver.mkTerm(
        Kind.EQUAL,
        solver.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
        solver.mkFiniteFieldElem(1, F),
    )
    aIsTwo = solver.mkTerm(
        Kind.EQUAL,
        a,
        solver.mkFiniteFieldElem(2, F),
    )
    solver.assertFormula(inv)
    solver.assertFormula(aIsTwo)
    r = solver.checkSat()
    assert r.isSat()
    assert solver.getValue(a).toPythonObj() == 2
    assert solver.getValue(b).toPythonObj() == -2

    bIsTwo = solver.mkTerm(
        Kind.EQUAL,
        b,
        solver.mkFiniteFieldElem(2, F),
    )
    solver.assertFormula(bIsTwo)
    r = solver.checkSat()
    assert not r.isSat()
