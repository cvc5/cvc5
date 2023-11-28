###############################################################################
# Top contributors (to current version):
#   Makai Mann, Alex Ozdemir, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

from fractions import Fraction
import pytest

import cvc5
from cvc5 import Kind


def testGetBool():
    solver = cvc5.Solver()
    t = solver.mkTrue()
    f = solver.mkFalse()
    assert t.toPythonObj() is True
    assert f.toPythonObj() is False


def testGetInt():
    solver = cvc5.Solver()
    two = solver.mkInteger(2)
    assert two.toPythonObj() == 2


def testGetReal():
    solver = cvc5.Solver()
    half = solver.mkReal("1/2")
    assert half.toPythonObj() == Fraction(1, 2)

    neg34 = solver.mkReal("-3/4")
    assert neg34.toPythonObj() == Fraction(-3, 4)

    neg1 = solver.mkInteger("-1")
    assert neg1.toPythonObj() == -1


def testGetBV():
    solver = cvc5.Solver()
    three = solver.mkBitVector(8, 3)
    assert three.toPythonObj() == 3


def testGetArray():
    solver = cvc5.Solver()
    arrsort = solver.mkArraySort(solver.getIntegerSort(), solver.getIntegerSort())
    zero_array = solver.mkConstArray(arrsort, solver.mkInteger(0))
    stores = solver.mkTerm(
            Kind.STORE, zero_array, solver.mkInteger(1), solver.mkInteger(2))
    stores = solver.mkTerm(
            Kind.STORE, stores, solver.mkInteger(2), solver.mkInteger(3))
    stores = solver.mkTerm(
            Kind.STORE, stores, solver.mkInteger(4), solver.mkInteger(5))

    array_dict = stores.toPythonObj()

    assert array_dict[1] == 2
    assert array_dict[2] == 3
    assert array_dict[4] == 5
    # an index that wasn't stored at should give zero
    assert array_dict[8] == 0


def testGetSymbol():
    solver = cvc5.Solver()
    solver.mkConst(solver.getBooleanSort(), "x")


def testGetString():
    solver = cvc5.Solver()

    s1 = '"test\n"😃\\u{a}'
    t1 = solver.mkString(s1)
    assert s1 == t1.toPythonObj()

    s2 = '❤️cvc5❤️'
    t2 = solver.mkString(s2)
    assert s2 == t2.toPythonObj()


def testGetValueInt():
    solver = cvc5.Solver()
    solver.setOption("produce-models", "true")

    intsort = solver.getIntegerSort()
    x = solver.mkConst(intsort, "x")
    solver.assertFormula(solver.mkTerm(Kind.EQUAL, x, solver.mkInteger(6)))

    r = solver.checkSat()
    assert r.isSat()

    xval = solver.getValue(x)
    assert xval.toPythonObj() == 6


def testGetValueReal():
    solver = cvc5.Solver()
    solver.setOption("produce-models", "true")

    realsort = solver.getRealSort()
    x = solver.mkConst(realsort, "x")
    y = solver.mkConst(realsort, "y")
    solver.assertFormula(solver.mkTerm(Kind.EQUAL, x, solver.mkReal("6")))
    solver.assertFormula(solver.mkTerm(Kind.EQUAL, y, solver.mkReal("8.33")))

    r = solver.checkSat()
    assert r.isSat()

    xval = solver.getValue(x)
    yval = solver.getValue(y)
    assert xval.toPythonObj() == Fraction("6")
    assert yval.toPythonObj() == Fraction("8.33")
