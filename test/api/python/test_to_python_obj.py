###############################################################################
# Top contributors (to current version):
#   Makai Mann, Andres Noetzli, Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

from fractions import Fraction
import pytest

import pycvc5
from pycvc5 import kinds


def testGetBool():
    solver = pycvc5.Solver()
    t = solver.mkTrue()
    f = solver.mkFalse()
    assert t.toPythonObj() == True
    assert f.toPythonObj() == False


def testGetInt():
    solver = pycvc5.Solver()
    two = solver.mkInteger(2)
    assert two.toPythonObj() == 2


def testGetReal():
    solver = pycvc5.Solver()
    half = solver.mkReal("1/2")
    assert half.toPythonObj() == Fraction(1, 2)

    neg34 = solver.mkReal("-3/4")
    assert neg34.toPythonObj() == Fraction(-3, 4)

    neg1 = solver.mkInteger("-1")
    assert neg1.toPythonObj() == -1


def testGetBV():
    solver = pycvc5.Solver()
    three = solver.mkBitVector(8, 3)
    assert three.toPythonObj() == 3


def testGetArray():
    solver = pycvc5.Solver()
    arrsort = solver.mkArraySort(solver.getRealSort(), solver.getRealSort())
    zero_array = solver.mkConstArray(arrsort, solver.mkInteger(0))
    stores = solver.mkTerm(kinds.Store, zero_array, solver.mkInteger(1), solver.mkInteger(2))
    stores = solver.mkTerm(kinds.Store, stores, solver.mkInteger(2), solver.mkInteger(3))
    stores = solver.mkTerm(kinds.Store, stores, solver.mkInteger(4), solver.mkInteger(5))

    array_dict = stores.toPythonObj()

    assert array_dict[1] == 2
    assert array_dict[2] == 3
    assert array_dict[4] == 5
    # an index that wasn't stored at should give zero
    assert array_dict[8] == 0


def testGetSymbol():
    solver = pycvc5.Solver()
    solver.mkConst(solver.getBooleanSort(), "x")


def testGetString():
    solver = pycvc5.Solver()

    s1 = '"test\n"😃\\u{a}'
    t1 = solver.mkString(s1)
    assert s1 == t1.toPythonObj()

    s2 = '❤️cvc5❤️'
    t2 = solver.mkString(s2)
    assert s2 == t2.toPythonObj()


def testGetValueInt():
    solver = pycvc5.Solver()
    solver.setOption("produce-models", "true")

    intsort = solver.getIntegerSort()
    x = solver.mkConst(intsort, "x")
    solver.assertFormula(solver.mkTerm(kinds.Equal, x, solver.mkInteger(6)))

    r = solver.checkSat()
    assert r.isSat()

    xval = solver.getValue(x)
    assert xval.toPythonObj() == 6


def testGetValueReal():
    solver = pycvc5.Solver()
    solver.setOption("produce-models", "true")

    realsort = solver.getRealSort()
    x = solver.mkConst(realsort, "x")
    y = solver.mkConst(realsort, "y")
    solver.assertFormula(solver.mkTerm(kinds.Equal, x, solver.mkReal("6")))
    solver.assertFormula(solver.mkTerm(kinds.Equal, y, solver.mkReal("8.33")))

    r = solver.checkSat()
    assert r.isSat()

    xval = solver.getValue(x)
    yval = solver.getValue(y)
    assert xval.toPythonObj() == Fraction("6")
    assert yval.toPythonObj() == Fraction("8.33")
