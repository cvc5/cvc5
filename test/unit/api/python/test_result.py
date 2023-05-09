###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Gereon Kremer, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for result API.
#
# Obtained by translating test/unit/api/result_black.cpp
##

import pytest
import cvc5
from cvc5 import Result
from cvc5 import UnknownExplanation


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_is_null(solver):
    res_null = Result(solver)
    assert res_null.isNull()
    assert not res_null.isSat()
    assert not res_null.isUnsat()
    assert not res_null.isUnknown()
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res = solver.checkSat()
    assert not res.isNull()


def test_eq(solver):
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res2 = solver.checkSat()
    res3 = solver.checkSat()
    res = Result()
    assert res != res2
    res = res2
    assert res == res2
    assert res3 == res2
    assert str(res) == "sat"


def test_is_sat(solver):
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res = solver.checkSat()
    assert res.isSat()
    assert not res.isUnknown()


def test_is_unsat(solver):
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    res = solver.checkSat()
    assert res.isUnsat()
    assert not res.isUnknown()


def test_is_sat_unknown(solver):
    solver.setLogic("QF_NIA")
    solver.setOption("incremental", "false")
    solver.setOption("solve-int-as-bv", "32")
    int_sort = solver.getIntegerSort()
    x = solver.mkConst(int_sort, "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    res = solver.checkSat()
    assert not res.isSat()
    assert res.isUnknown()
    ue = res.getUnknownExplanation()
    assert ue == UnknownExplanation.UNKNOWN_REASON
    assert str(ue) == "UnknownExplanation.UNKNOWN_REASON"
