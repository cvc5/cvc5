###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir, Aina Niemetz, Alex Sokolov
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
from cvc5 import Sort, Term, Kind


@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def test_basic_finite_field(tm, solver):
    solver.setOption("produce-models", "true")
    F = tm.mkFiniteFieldSort(5)
    a = tm.mkConst(F, "a")
    b = tm.mkConst(F, "b")
    assert 5 == F.getFiniteFieldSize()

    inv = tm.mkTerm(
        Kind.EQUAL,
        tm.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
        tm.mkFiniteFieldElem(1, F),
    )
    aIsTwo = tm.mkTerm(
        Kind.EQUAL,
        a,
        tm.mkFiniteFieldElem(2, F),
    )
    solver.assertFormula(inv)
    solver.assertFormula(aIsTwo)
    r = solver.checkSat()
    assert r.isSat()
    assert solver.getValue(a).toPythonObj() == 2
    assert solver.getValue(b).toPythonObj() == -2

    bIsTwo = tm.mkTerm(
        Kind.EQUAL,
        b,
        tm.mkFiniteFieldElem(2, F),
    )
    solver.assertFormula(bIsTwo)
    r = solver.checkSat()
    assert not r.isSat()

def test_basic_finite_field_base(tm, solver):
    solver.setOption("produce-models", "true")
    F = tm.mkFiniteFieldSort("101", 2)
    a = tm.mkConst(F, "a")
    b = tm.mkConst(F, "b")
    assert 5 == F.getFiniteFieldSize()

    inv = tm.mkTerm(
        Kind.EQUAL,
        tm.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
        tm.mkFiniteFieldElem("1", F, 3),
    )
    aIsTwo = tm.mkTerm(
        Kind.EQUAL,
        a,
        tm.mkFiniteFieldElem("10", F, 2),
    )
    solver.assertFormula(inv)
    solver.assertFormula(aIsTwo)
    r = solver.checkSat()
    assert r.isSat()
    assert solver.getValue(a).toPythonObj() == 2
    assert solver.getValue(b).toPythonObj() == -2

    bIsTwo = tm.mkTerm(
        Kind.EQUAL,
        b,
        tm.mkFiniteFieldElem(2, F),
    )
    solver.assertFormula(bIsTwo)
    r = solver.checkSat()
    assert not r.isSat()

def test_finite_field_base_equality(tm):
    F = tm.mkFiniteFieldSort("11", 4)
    c = tm.mkFiniteFieldElem("-6d", F, 16)
    d = tm.mkFiniteFieldElem("1", F, 16)
    assert c == d

