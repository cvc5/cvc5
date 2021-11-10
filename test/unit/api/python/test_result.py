###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
import pycvc5
from pycvc5 import kinds
from pycvc5 import Result
from pycvc5 import UnknownExplanation


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_is_null(solver):
    res_null = Result(solver)
    assert res_null.isNull()
    assert not res_null.isSat()
    assert not res_null.isUnsat()
    assert not res_null.isSatUnknown()
    assert not res_null.isEntailed()
    assert not res_null.isNotEntailed()
    assert not res_null.isEntailmentUnknown()
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkVar(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res = solver.checkSat()
    assert not res.isNull()


def test_eq(solver):
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkVar(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res2 = solver.checkSat()
    res3 = solver.checkSat()
    res = res2
    assert res == res2
    assert res3 == res2


def test_is_sat(solver):
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkVar(u_sort, "x")
    solver.assertFormula(x.eqTerm(x))
    res = solver.checkSat()
    assert res.isSat()
    assert not res.isSatUnknown()


def test_is_unsat(solver):
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkVar(u_sort, "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    res = solver.checkSat()
    assert res.isUnsat()
    assert not res.isSatUnknown()


def test_is_sat_unknown(solver):
    solver.setLogic("QF_NIA")
    solver.setOption("incremental", "false")
    solver.setOption("solve-int-as-bv", "32")
    int_sort = solver.getIntegerSort()
    x = solver.mkVar(int_sort, "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    res = solver.checkSat()
    assert not res.isSat()
    assert res.isSatUnknown()


def test_is_entailed(solver):
    solver.setOption("incremental", "true")
    u_sort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(u_sort, "x")
    y = solver.mkConst(u_sort, "y")
    a = x.eqTerm(y).notTerm()
    b = x.eqTerm(y)
    solver.assertFormula(a)
    entailed = solver.checkEntailed(a)
    assert entailed.isEntailed()
    assert not entailed.isEntailmentUnknown()
    not_entailed = solver.checkEntailed(b)
    assert not_entailed.isNotEntailed()
    assert not not_entailed.isEntailmentUnknown()


def test_is_entailment_unknown(solver):
    solver.setLogic("QF_NIA")
    solver.setOption("incremental", "false")
    solver.setOption("solve-int-as-bv", "32")
    int_sort = solver.getIntegerSort()
    x = solver.mkVar(int_sort, "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    res = solver.checkEntailed(x.eqTerm(x))
    assert not res.isEntailed()
    assert res.isEntailmentUnknown()
    print(type(pycvc5.RoundTowardZero))
    print(type(pycvc5.UnknownReason))
    assert res.getUnknownExplanation() == pycvc5.UnknownReason
