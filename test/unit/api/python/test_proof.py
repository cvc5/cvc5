###############################################################################
# Top contributors (to current version):
#   Hans-Jörg Schurr, Ying Sheng, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for proof API.
#
# Obtained by translating test/unit/api/sort_black.cpp
##

import pytest
import cvc5
from cvc5 import Kind


@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def create_proof(tm, solver):
    solver.setOption("produce-proofs", "true");

    uSort = tm.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    uToIntSort = tm.mkFunctionSort(uSort, intSort)
    intPredSort = tm.mkFunctionSort(intSort, boolSort)

    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    f = tm.mkConst(uToIntSort, "f")
    p = tm.mkConst(intPredSort, "p")
    zero = tm.mkInteger(0)
    one = tm.mkInteger(1)
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    summ = tm.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)
    solver.assertFormula(tm.mkTerm(Kind.GT, zero, f_x))
    solver.assertFormula(tm.mkTerm(Kind.GT, zero, f_y))
    solver.assertFormula(tm.mkTerm(Kind.GT, summ, one))
    solver.assertFormula(p_0)
    solver.assertFormula(p_f_y.notTerm())
    assert solver.checkSat().isUnsat()

    return solver.getProof()[0]


def test_get_result(tm, solver):
    proof = create_proof(tm, solver)
    rule = proof.getRule()
    assert rule == "SCOPE"


def test_get_result(tm, solver):
    proof = create_proof(tm, solver)
    proof.getResult()


def test_get_children(tm, solver):
    proof = create_proof(tm, solver)
    children = proof.getChildren()
    assert len(children) > 0


def test_get_arguments(tm, solver):
    proof = create_proof(tm, solver)
    proof.getArguments()
