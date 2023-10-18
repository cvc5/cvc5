###############################################################################
# Top contributors (to current version):
#   Hans-Jörg Schurr
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
def solver():
    return cvc5.Solver()


def create_proof(solver):
    solver.setOption("produce-proofs", "true");

    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    f_y = solver.mkTerm(Kind.APPLY_UF, f, y)
    summ = solver.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = solver.mkTerm(Kind.APPLY_UF, p, f_y)
    solver.assertFormula(solver.mkTerm(Kind.GT, zero, f_x))
    solver.assertFormula(solver.mkTerm(Kind.GT, zero, f_y))
    solver.assertFormula(solver.mkTerm(Kind.GT, summ, one))
    solver.assertFormula(p_0)
    solver.assertFormula(p_f_y.notTerm())
    assert solver.checkSat().isUnsat()

    return solver.getProof()[0]


def test_get_result(solver):
    proof = create_proof(solver)
    rule = proof.getRule()
    assert rule == "SCOPE"


def test_get_result(solver):
    proof = create_proof(solver)
    proof.getResult()


def test_get_children(solver):
    proof = create_proof(solver)
    children = proof.getChildren()
    assert len(children) > 0


def test_get_arguments(solver):
    proof = create_proof(solver)
    proof.getArguments()
