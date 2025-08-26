###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Makai Mann, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

from fractions import Fraction
import pytest

import cvc5
from cvc5 import Kind

@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)

def testGetBool(tm):
    t = tm.mkTrue()
    f = tm.mkFalse()
    assert t.toPythonObj() is True
    assert f.toPythonObj() is False


def testGetInt(tm):
    two = tm.mkInteger(2)
    assert two.toPythonObj() == 2


def testGetReal(tm):
    half = tm.mkReal("1/2")
    assert half.toPythonObj() == Fraction(1, 2)
    neg34 = tm.mkReal("-3/4")
    assert neg34.toPythonObj() == Fraction(-3, 4)
    neg1 = tm.mkInteger("-1")
    assert neg1.toPythonObj() == -1


def testGetBV(tm):
    three = tm.mkBitVector(8, 3)
    assert three.toPythonObj() == 3


def testGetArray(tm):
    arrsort = tm.mkArraySort(tm.getIntegerSort(), tm.getIntegerSort())
    zero_array = tm.mkConstArray(arrsort, tm.mkInteger(0))
    stores = tm.mkTerm(
            Kind.STORE, zero_array, tm.mkInteger(1), tm.mkInteger(2))
    stores = tm.mkTerm(
            Kind.STORE, stores, tm.mkInteger(2), tm.mkInteger(3))
    stores = tm.mkTerm(
            Kind.STORE, stores, tm.mkInteger(4), tm.mkInteger(5))

    array_dict = stores.toPythonObj()

    assert array_dict[1] == 2
    assert array_dict[2] == 3
    assert array_dict[4] == 5
    # an index that wasn't stored at should give zero
    assert array_dict[8] == 0


def testGetSymbol(tm):
    tm.mkConst(tm.getBooleanSort(), "x")


def testGetString(tm):
    s1 = '"test\n"😃\\u{a}'
    t1 = tm.mkString(s1)
    assert s1 == t1.toPythonObj()

    s2 = '❤️cvc5❤️'
    t2 = tm.mkString(s2)
    assert s2 == t2.toPythonObj()


def testGetValueInt(tm, solver):
    solver.setOption("produce-models", "true")

    intsort = tm.getIntegerSort()
    x = tm.mkConst(intsort, "x")
    solver.assertFormula(tm.mkTerm(Kind.EQUAL, x, tm.mkInteger(6)))

    r = solver.checkSat()
    assert r.isSat()

    xval = solver.getValue(x)
    assert xval.toPythonObj() == 6


def testGetValueReal(tm, solver):
    solver.setOption("produce-models", "true")

    realsort = solver.getRealSort()
    x = tm.mkConst(realsort, "x")
    y = tm.mkConst(realsort, "y")
    solver.assertFormula(tm.mkTerm(Kind.EQUAL, x, tm.mkReal("6")))
    solver.assertFormula(tm.mkTerm(Kind.EQUAL, y, tm.mkReal("8.33")))

    r = solver.checkSat()
    assert r.isSat()

    xval = solver.getValue(x)
    yval = solver.getValue(y)
    assert xval.toPythonObj() == Fraction("6")
    assert yval.toPythonObj() == Fraction("8.33")
