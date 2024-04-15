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
from cvc5 import Kind, ProofRule


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


def create_rewrite_proof(tm, solver):
    solver.setOption("produce-proofs", "true")
    solver.setOption("proof-granularity", "dsl-rewrite")
    int_sort = tm.getIntegerSort()
    x = tm.mkConst(int_sort, "x")
    two_x = tm.mkTerm(Kind.MULT, tm.mkInteger(2), x)
    x_plus_x = tm.mkTerm(Kind.ADD, x, x)
    solver.assertFormula(tm.mkTerm(Kind.DISTINCT, two_x, x_plus_x))
    solver.checkSat()
    return solver.getProof()[0]


def test_get_result(tm, solver):
    proof = create_proof(tm, solver)
    rule = proof.getRule()
    assert rule == "SCOPE"


def test_get_proof_rewrite_rule(tm, solver):
    proof = create_rewrite_proof(tm, solver)
    with pytest.raises(RuntimeError):
        proof.getProofRewriteRule()
    rule = None
    stack = [proof]
    while rule != ProofRule.DSL_REWRITE:
        proof = stack.pop()
        rule = proof.getRule()
        children = proof.getChildren()
        stack.extend(children)
    assert proof.getProofRewriteRule() is not None


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
