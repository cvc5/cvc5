###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Lifetime tests for the Python API.
#
# Python wrappers (Term, Sort, Op, Datatype, Grammar, Proof, ...) hold a
# reference to their TermManager, and the underlying C++ objects additionally
# keep the internal node manager alive. CPython's deterministic reference
# counting lets us drop the term manager / solver references at a precise
# point (``del`` followed by an explicit ``gc.collect()`` to break any cycles)
# and then verify that objects derived from them remain usable.
#
# Note: the Python wrappers also hold a reference to the TermManager, so these
# tests primarily exercise that binding-level keepalive; the underlying native
# shared_ptr guarantee is proven by the C++ and Java suites.
#
# Mirrors test/unit/api/cpp/api_lifetime_black.cpp.
##

import gc
import pytest
import cvc5

from cvc5 import Kind, TermManager, Solver


def test_sort_outlives_term_manager():
    tm = TermManager()
    s = tm.getIntegerSort()
    arr = tm.mkArraySort(s, tm.getBooleanSort())
    del tm
    gc.collect()
    assert s.isInteger()
    assert arr.isArray()
    assert s == arr.getArrayIndexSort()
    assert str(s)


def test_term_outlives_term_manager():
    tm = TermManager()
    int_sort = tm.getIntegerSort()
    x = tm.mkConst(int_sort, "x")
    t = tm.mkTerm(Kind.ADD, x, tm.mkInteger(1))
    del tm
    gc.collect()
    assert t.getKind() == Kind.ADD
    assert t.getSort() == int_sort
    assert t.getNumChildren() == 2
    assert str(t)


def test_op_outlives_term_manager():
    tm = TermManager()
    op = tm.mkOp(Kind.BITVECTOR_EXTRACT, 4, 0)
    del tm
    gc.collect()
    assert op.isIndexed()
    assert op.getKind() == Kind.BITVECTOR_EXTRACT
    assert op.getNumIndices() == 2
    assert op[0] is not None
    assert str(op)


def test_term_iterator_outlives_term_manager():
    tm = TermManager()
    b = tm.getBooleanSort()
    t = tm.mkTerm(Kind.AND, tm.mkConst(b, "x"), tm.mkConst(b, "y"))
    del tm
    gc.collect()
    count = 0
    for child in t:
        assert not child.isNull()
        count += 1
    assert count == 2


def test_datatype_outlives_term_manager():
    tm = TermManager()
    decl = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", tm.getIntegerSort())
    cons.addSelectorSelf("tail")
    decl.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    decl.addConstructor(nil)
    list_sort = tm.mkDatatypeSort(decl)
    del tm
    gc.collect()
    dt = list_sort.getDatatype()
    assert dt.getName() == "list"
    assert dt.getNumConstructors() == 2

    num_ctors = 0
    for ctor in dt:
        assert ctor.getName()
        for sel in ctor:
            assert sel.getName()
        num_ctors += 1
    assert num_ctors == 2

    cons_ctor = dt.getConstructor("cons")
    assert cons_ctor.getName() == "cons"
    head = cons_ctor.getSelector("head")
    assert head.getName() == "head"
    assert head.getCodomainSort().isInteger()


def test_solver_outlives_term_manager():
    tm = TermManager()
    solver = Solver(tm)
    del tm
    gc.collect()
    tm2 = solver.getTermManager()
    x = tm2.mkConst(tm2.getBooleanSort(), "x")
    solver.assertFormula(x)
    assert solver.checkSat().isSat()


def test_value_outlives_solver_and_term_manager():
    tm = TermManager()
    solver = Solver(tm)
    solver.setOption("produce-models", "true")
    int_sort = tm.getIntegerSort()
    x = tm.mkConst(int_sort, "x")
    solver.assertFormula(tm.mkTerm(Kind.GT, x, tm.mkInteger(0)))
    assert solver.checkSat().isSat()
    value = solver.getValue(x)
    del solver
    del tm
    gc.collect()
    assert not value.isNull()
    assert value.getSort().isInteger()
    assert str(value)


def test_grammar_outlives_solver_and_term_manager():
    tm = TermManager()
    solver = Solver(tm)
    solver.setOption("sygus", "true")
    b = tm.getBooleanSort()
    start = tm.mkVar(b)
    g = solver.mkGrammar([], [start])
    g.addRule(start, tm.mkBoolean(False))
    del solver
    del tm
    gc.collect()
    assert str(g) != ""


def test_proof_outlives_solver_and_term_manager():
    tm = TermManager()
    solver = Solver(tm)
    solver.setOption("produce-proofs", "true")
    b = tm.getBooleanSort()
    x = tm.mkConst(b, "x")
    solver.assertFormula(x)
    solver.assertFormula(x.notTerm())
    assert not solver.checkSat().isSat()
    proof = solver.getProof()[0]
    del solver
    del tm
    gc.collect()
    proof.getRule()
    proof.getResult()
    proof.getChildren()


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__]))
