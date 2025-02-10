###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
from cvc5 import Kind, UnknownExplanation


@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def test_is_null(tm, solver):
    res_null = Result(solver)
    assert res_null.isNull()
    assert not res_null.isSat()
    assert not res_null.isUnsat()
    assert not res_null.isUnknown()
    u_sort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res = solver.checkSat()
    assert not res.isNull()


def test_eq(tm, solver):
    u_sort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res2 = solver.checkSat()
    res3 = solver.checkSat()
    res = Result()
    assert res != res2
    res = res2
    assert res == res2
    assert res3 == res2
    assert str(res) == "sat"


def test_is_sat(tm, solver):
    u_sort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res = solver.checkSat()
    assert res.isSat()
    assert not res.isUnknown()


def test_is_unsat(tm, solver):
    u_sort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(u_sort, "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    res = solver.checkSat()
    assert res.isUnsat()
    assert not res.isUnknown()


def test_is_sat_unknown(tm, solver):
    solver.setLogic("QF_NIA")
    solver.setOption("incremental", "false")
    solver.setOption("solve-real-as-int", "true")
    real_sort = tm.getRealSort()
    x = tm.mkConst(real_sort, "x")
    solver.assertFormula(tm.mkTerm(Kind.LT, tm.mkReal("0.0"), x))
    solver.assertFormula(tm.mkTerm(Kind.LT, x, tm.mkReal("1.0")))
    res = solver.checkSat()
    assert not res.isSat()
    assert res.isUnknown()
    ue = res.getUnknownExplanation()
    assert ue == UnknownExplanation.INCOMPLETE
    assert str(ue) == "UnknownExplanation.INCOMPLETE"
