###############################################################################
# Top contributors (to current version):
#   Ying Sheng, Yoni Zohar, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
import sys
from math import isnan

from cvc5 import Kind, SortKind, TermManager, Solver, Plugin
from cvc5 import RoundingMode
from cvc5 import BlockModelsMode, LearnedLitType, FindSynthTarget
from cvc5 import ProofComponent, ProofFormat


@pytest.fixture
def tm():
    return TermManager()
@pytest.fixture
def solver(tm):
    return Solver(tm)


def test_recoverable_exception(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    with pytest.raises(RuntimeError):
        c = solver.getValue(x)


def test_declare_fun_fresh(tm, solver):
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    t1 = solver.declareFun("b", [], boolSort, True)
    t2 = solver.declareFun("b", [], boolSort, False)
    t3 = solver.declareFun("b", [], boolSort, False)
    assert not t1 == t2
    assert not t1 == t3
    assert t2 == t3
    t4 = solver.declareFun("c", [], boolSort, False)
    assert not t2 == t4
    t5 = solver.declareFun("b", [], intSort, False)
    assert not t2 == t5

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.declareFun("b", [], intSort, False)


def test_declare_fun(tm, solver):
    bvSort = tm.mkBitVectorSort(32)
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),\
                                    tm.getIntegerSort())
    solver.declareFun("f1", [], bvSort)
    solver.declareFun("f3", [bvSort, tm.getIntegerSort()], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f2", [], funSort)
    # functions as arguments is allowed
    solver.declareFun("f4", [bvSort, funSort], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f5", [bvSort, bvSort], funSort)
    slv = Solver(tm)
    slv.declareFun("f1", [], bvSort)

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.declareFun("f1", [], bvSort)


def decalre_datatype(tm, solver):
    lin = tm.mkDatatypeConstructorDecl("lin")
    solver.declareDatatype("", [lin])

    nil = tm.mkDatatypeConstructorDecl("nil")
    solver.declareDatatype("a", [nil])

    cons = tm.mkDatatypeConstructorDecl("cons")
    nil2 = tm.mkDatatypeConstructorDecl("nil")
    solver.declareDatatype("b", [cons, nil2])

    cons2 = tm.mkDatatypeConstructorDecl("cons")
    nil3 = tm.mkDatatypeConstructorDecl("nil")
    solver.declareDatatype("", [cons2, nil3])

    # must have at least one constructor
    with pytest.raises(RuntimeError):
        solver.declareDatatype("c", [])
    # constructors may not be reused
    ctor1 = tm.mkDatatypeConstructorDecl("_x21")
    ctor2 = tm.mkDatatypeConstructorDecl("_x31")
    s3 = solver.declareDatatype("_x17", [ctor1, ctor2])
    with pytest.raises(RuntimeError):
        solver.declareDatatype("_x86", [ctor1, ctor2])

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    nnil = tm.mkDatatypeConstructorDecl("nil")
    slv.declareDatatype("a", [nnil])


def test_declare_sort(solver):
    solver.declareSort("s", 0)
    solver.declareSort("s", 2)
    solver.declareSort("", 2)


def test_declare_sort_fresh(solver):
    t1 = solver.declareSort("b", 0, True)
    t2 = solver.declareSort("b", 0, False)
    t3 = solver.declareSort("b", 0, False)
    assert t1!=t2
    assert t1!=t3
    assert t2==t3
    t4 = solver.declareSort("c", 0, False)
    assert t2!=t4
    t5 = solver.declareSort("b", 1, False)
    assert t2!=t5


def test_define_fun(tm, solver):
    bvSort = tm.mkBitVectorSort(32)
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),
                                    tm.getIntegerSort())
    b1 = tm.mkVar(bvSort, "b1")
    b2 = tm.mkVar(tm.getIntegerSort(), "b2")
    b3 = tm.mkVar(funSort, "b3")
    v1 = tm.mkConst(bvSort, "v1")
    v2 = tm.mkConst(funSort, "v2")
    solver.defineFun("f", [], bvSort, v1)
    solver.defineFun("ff", [b1, b2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("ff", [v1, b2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("fff", [b1], bvSort, v2)
    with pytest.raises(RuntimeError):
        solver.defineFun("ffff", [b1], funSort, v2)
    # b3 has function sort, which is allowed as an argument
    solver.defineFun("fffff", [b1, b3], bvSort, v1)

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    bvSort2 = ttm.mkBitVectorSort(32)
    v12 = ttm.mkConst(bvSort2, "v1")
    b12 = ttm.mkVar(bvSort2, "b1")
    b22 = ttm.mkVar(ttm.getIntegerSort(), "b2")
    #with pytest.raises(RuntimeError):
    slv.defineFun("f", [], bvSort, v12)
    #with pytest.raises(RuntimeError):
    slv.defineFun("f", [], bvSort2, v1)
    #with pytest.raises(RuntimeError):
    slv.defineFun("ff", [b1, b22], bvSort2, v12)
    #with pytest.raises(RuntimeError):
    slv.defineFun("ff", [b12, b2], bvSort2, v12)
    #with pytest.raises(RuntimeError):
    slv.defineFun("ff", [b12, b22], bvSort, v12)
    #with pytest.raises(RuntimeError):
    slv.defineFun("ff", [b12, b22], bvSort2, v1)


def test_define_fun_global(tm, solver):
    bSort = solver.getBooleanSort()

    bTrue = tm.mkBoolean(True)
    # (define-fun f () Bool true)
    f = solver.defineFun("f", [], bSort, bTrue, True)
    b = tm.mkVar(bSort, "b")
    # (define-fun g (b Bool) Bool b)
    g = solver.defineFun("g", [b], bSort, b, True)

    # (assert (or (not f) (not (g true))))
    solver.assertFormula(
        tm.mkTerm(Kind.OR, f.notTerm(),
                      tm.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
    assert solver.checkSat().isUnsat()
    solver.resetAssertions()
    # (assert (or (not f) (not (g true))))
    solver.assertFormula(
        tm.mkTerm(Kind.OR, f.notTerm(),
                      tm.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
    assert solver.checkSat().isUnsat()

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.defineFun("f", [], bSort, bTrue, True)


def test_define_fun_rec(tm, solver):
    bvSort = tm.mkBitVectorSort(32)
    funSort1 = tm.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = tm.mkFunctionSort(
            tm.mkUninterpretedSort("u"), tm.getIntegerSort())
    b1 = tm.mkVar(bvSort, "b1")
    b11 = tm.mkVar(bvSort, "b1")
    b2 = tm.mkVar(tm.getIntegerSort(), "b2")
    b3 = tm.mkVar(funSort2, "b3")
    v1 = tm.mkConst(bvSort, "v1")
    v2 = tm.mkConst(tm.getIntegerSort(), "v2")
    v3 = tm.mkConst(funSort2, "v3")
    f1 = tm.mkConst(funSort1, "f1")
    f2 = tm.mkConst(funSort2, "f2")
    f3 = tm.mkConst(bvSort, "f3")
    solver.defineFunRec("f", [], bvSort, v1)
    solver.defineFunRec("ff", [b1, b2], bvSort, v1)
    solver.defineFunRec(f1, [b1, b11], v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec("fff", [b1], bvSort, v3)
    with pytest.raises(RuntimeError):
        solver.defineFunRec("ff", [b1, v2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec("ffff", [b1], funSort2, v3)
    # b3 has function sort, which is allowed as an argument
    solver.defineFunRec("fffff", [b1, b3], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f1, [b1], v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f1, [b1, b11], v2)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f1, [b1, b11], v3)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f2, [b1], v2)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f3, [b1], v1)

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    bvSort2 = ttm.mkBitVectorSort(32)
    v12 = ttm.mkConst(bvSort2, "v1")
    b12 = ttm.mkVar(bvSort2, "b1")
    b22 = ttm.mkVar(tm.getIntegerSort(), "b2")
    slv.defineFunRec("f", [], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort2, v12)
    slv.defineFunRec("f", [], bvSort, v12)
    slv.defineFunRec("f", [], bvSort2, v1)
    slv.defineFunRec("ff", [b1, b22], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b2], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort2, v1)


def test_define_fun_rec_wrong_logic(tm, solver):
    solver.setLogic("QF_BV")
    bvSort = tm.mkBitVectorSort(32)
    funSort = tm.mkFunctionSort([bvSort, bvSort], bvSort)
    b = tm.mkVar(bvSort, "b")
    v = tm.mkConst(bvSort, "v")
    f = tm.mkConst(funSort, "f")
    with pytest.raises(RuntimeError):
        solver.defineFunRec("f", [], bvSort, v)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f, [b, b], v)


def test_define_fun_rec_global(tm, solver):
    bSort = tm.getBooleanSort()
    fSort = tm.mkFunctionSort([bSort], bSort)

    solver.push()
    bTrue = tm.mkBoolean(True)
    # (define-fun f () Bool true)
    f = solver.defineFunRec("f", [], bSort, bTrue, True)
    b = tm.mkVar(bSort, "b")
    gSym = tm.mkConst(fSort, "g")
    # (define-fun g (b Bool) Bool b)
    g = solver.defineFunRec(gSym, [b], b, glbl=True)

    # (assert (or (not f) (not (g true))))
    solver.assertFormula(tm.mkTerm(
        Kind.OR, f.notTerm(), tm.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
    assert solver.checkSat().isUnsat()
    solver.pop()
    # (assert (or (not f) (not (g true))))
    solver.assertFormula(tm.mkTerm(
        Kind.OR, f.notTerm(), tm.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
    assert solver.checkSat().isUnsat()

    ttm = TermManager()
    slv = Solver(ttm)
    bb = ttm.mkVar(tm.getBooleanSort(), "b")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.defineFunRec(
      tm.mkConst(
          tm.mkFunctionSort({tm.getBooleanSort()}, tm.getBooleanSort()),
          "g"),
      [bb],
      bb,
      True)
    slv.defineFunRec(
      ttm.mkConst(ttm.mkFunctionSort({ttm.getBooleanSort()}, ttm.getBooleanSort()),
                 "g"),
      [b],
      b,
      True)


def test_define_funs_rec(tm, solver):
    uSort = tm.mkUninterpretedSort("u")
    bvSort = tm.mkBitVectorSort(32)
    funSort1 = tm.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = tm.mkFunctionSort([uSort], tm.getIntegerSort())
    b1 = tm.mkVar(bvSort, "b1")
    b11 = tm.mkVar(bvSort, "b1")
    b2 = tm.mkVar(tm.getIntegerSort(), "b2")
    b3 = tm.mkVar(funSort2, "b3")
    b4 = tm.mkVar(uSort, "b4")
    v1 = tm.mkConst(bvSort, "v1")
    v2 = tm.mkConst(tm.getIntegerSort(), "v2")
    v3 = tm.mkConst(funSort2, "v3")
    v4 = tm.mkConst(uSort, "v4")
    f1 = tm.mkConst(funSort1, "f1")
    f2 = tm.mkConst(funSort2, "f2")
    f3 = tm.mkConst(bvSort, "f3")
    solver.defineFunsRec([f1, f2], [[b1, b11], [b4]], [v1, v2])
    with pytest.raises(RuntimeError):
      solver.defineFunsRec([f1, f2], [[v1, b11], [b4]], [v1, v2])
    with pytest.raises(RuntimeError):
      solver.defineFunsRec([f1, f3], [[b1, b11], [b4]], [v1, v2])
    with pytest.raises(RuntimeError):
      solver.defineFunsRec([f1, f2], [[b1], [b4]], [v1, v2])
    with pytest.raises(RuntimeError):
      solver.defineFunsRec([f1, f2], [[b1, b2], [b4]], [v1, v2])
    with pytest.raises(RuntimeError):
      solver.defineFunsRec([f1, f2], [[b1, b11], [b4]], [v1, v4])

    ttm = TermManager()
    slv = Solver(ttm)
    bb = ttm.mkVar(tm.getBooleanSort(), "b")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    uSort2 = ttm.mkUninterpretedSort("u")
    bvSort2 = ttm.mkBitVectorSort(32)
    funSort12 = ttm.mkFunctionSort([bvSort2, bvSort2], bvSort2)
    funSort22 = ttm.mkFunctionSort([uSort2], ttm.getIntegerSort())
    b12 = ttm.mkVar(bvSort2, "b1")
    b112 = ttm.mkVar(bvSort2, "b1")
    b42 = ttm.mkVar(uSort2, "b4")
    v12 = ttm.mkConst(bvSort2, "v1")
    v22 = ttm.mkConst(ttm.getIntegerSort(), "v2")
    f12 = ttm.mkConst(funSort12, "f1")
    f22 = ttm.mkConst(funSort22, "f2")
    slv.defineFunsRec([f12, f22], [[b12, b112], [b42]], [v12, v22])
    slv.defineFunsRec([f1, f22], [[b12, b112], [b42]], [v12, v22])
    slv.defineFunsRec([f12, f22], [[b1, b112], [b42]], [v12, v22])
    slv.defineFunsRec([f12, f22], [[b12, b11], [b42]], [v12, v22])
    slv.defineFunsRec([f12, f22], [[b12, b112], [b42]], [v1, v22])
    slv.defineFunsRec([f12, f22], [[b12, b112], [b42]], [v12, v2])
    with pytest.raises(RuntimeError):
      slv.defineFunsRec([f12, f2], [[b12, b112], [b42]], [v12, v22])
    with pytest.raises(RuntimeError):
      slv.defineFunsRec([f12, f22], [[b12, b112], [b4]], [v12, v22])


def test_define_funs_rec_wrong_logic(tm, solver):
  solver.setLogic("QF_BV")
  uSort = tm.mkUninterpretedSort("u")
  bvSort = tm.mkBitVectorSort(32)
  funSort1 = tm.mkFunctionSort([bvSort, bvSort], bvSort)
  funSort2 = tm.mkFunctionSort([uSort], tm.getIntegerSort())
  b = tm.mkVar(bvSort, "b")
  u = tm.mkVar(uSort, "u")
  v1 = tm.mkConst(bvSort, "v1")
  v2 = tm.mkConst(tm.getIntegerSort(), "v2")
  f1 = tm.mkConst(funSort1, "f1")
  f2 = tm.mkConst(funSort2, "f2")
  with pytest.raises(RuntimeError):
    solver.defineFunsRec([f1, f2], [[b, b], [u]], [v1, v2])


def test_define_funs_rec_global(tm, solver):
  bSort = tm.getBooleanSort()
  fSort = tm.mkFunctionSort([bSort], bSort)

  solver.push()
  bTrue = tm.mkBoolean(True)
  b = tm.mkVar(bSort, "b")
  gSym = tm.mkConst(fSort, "g")
  # (define-funs-rec ((g ((b Bool)) Bool)) (b))
  solver.defineFunsRec([gSym], [[b]], [b], True)

  # (assert (not (g true)))
  solver.assertFormula(tm.mkTerm(Kind.APPLY_UF, gSym, bTrue).notTerm())
  assert solver.checkSat().isUnsat()
  solver.pop()
  # (assert (not (g true)))
  solver.assertFormula(tm.mkTerm(Kind.APPLY_UF, gSym, bTrue).notTerm())
  assert solver.checkSat().isUnsat()


def test_get_assertions(tm, solver):
    a = tm.mkConst(tm.getBooleanSort(), 'a')
    b = tm.mkConst(tm.getBooleanSort(), 'b')
    solver.assertFormula(a)
    solver.assertFormula(b)
    asserts = [a,b]
    assert solver.getAssertions() == asserts


def test_get_info(solver):
    solver.getInfo("name")
    with pytest.raises(RuntimeError):
        solver.getInfo("asdf")


def test_get_option(solver):
    solver.setOption("incremental", "true")
    assert solver.getOption("incremental") == "true"
    with pytest.raises(RuntimeError):
        solver.getOption("asdf")


def test_get_option_names(solver):
    opts = solver.getOptionNames()
    assert len(opts) > 100
    assert "verbose" in opts
    assert "foobar" not in opts


def test_get_option_info(solver):
    with pytest.raises(RuntimeError):
        solver.getOptionInfo("asdf-invalid")

    info = solver.getOptionInfo("verbose")
    assert info['name'] == "verbose"
    assert info['aliases'] == []
    assert not info['setByUser']
    assert info['type'] is None

    info = solver.getOptionInfo("print-success")
    assert info['name'] == "print-success"
    assert info['aliases'] == []
    assert not info['setByUser']
    assert info['type'] is bool
    assert info['current'] == False
    assert info['default'] == False

    info = solver.getOptionInfo("verbosity")
    assert info['name'] == "verbosity"
    assert info['aliases'] == []
    assert not info['setByUser']
    assert info['type'] is int
    assert info['current'] == 0
    assert info['default'] == 0
    assert info['minimum'] is None and info['maximum'] is None

    info = solver.getOptionInfo("rlimit")
    assert info['name'] == "rlimit"
    assert info['aliases'] == []
    assert not info['setByUser']
    assert info['type'] is int
    assert info['current'] == 0
    assert info['default'] == 0
    assert info['minimum'] is None and info['maximum'] is None

    info = solver.getOptionInfo("random-freq")
    assert info['name'] == "random-freq"
    assert info['aliases'] == ["random-frequency"]
    assert not info['setByUser']
    assert info['type'] is float
    assert info['current'] == 0.0
    assert info['default'] == 0.0
    assert info['minimum'] == 0.0 and info['maximum'] == 1.0

    info = solver.getOptionInfo("force-logic")
    assert info['name'] == "force-logic"
    assert info['aliases'] == []
    assert not info['setByUser']
    assert info['type'] is str
    assert info['current'] == ""
    assert info['default'] == ""

    info = solver.getOptionInfo("simplification")
    assert info['name'] == "simplification"
    assert info['aliases'] == ["simplification-mode"]
    assert not info['setByUser']
    assert info['type'] == 'mode'
    assert info['current'] == 'batch'
    assert info['default'] == 'batch'
    assert info['modes'] == ['batch', 'none']


def test_get_unsat_assumptions1(solver):
    solver.setOption("incremental", "false")
    solver.checkSatAssuming(solver.mkFalse())
    with pytest.raises(RuntimeError):
        solver.getUnsatAssumptions()


def test_get_unsat_assumptions2(solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-assumptions", "false")
    solver.checkSatAssuming(solver.mkFalse())
    with pytest.raises(RuntimeError):
        solver.getUnsatAssumptions()


def test_get_unsat_assumptions3(solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-assumptions", "true")
    solver.checkSatAssuming(solver.mkFalse())
    solver.getUnsatAssumptions()
    solver.checkSatAssuming(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.getUnsatAssumptions()


def test_get_unsat_core1(solver):
    solver.setOption("incremental", "false")
    solver.assertFormula(solver.mkFalse())
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getUnsatCore()


def test_get_unsat_core2(solver):
    solver.setOption("incremental", "false")
    solver.setOption("produce-unsat-cores", "false")
    solver.assertFormula(solver.mkFalse())
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getUnsatCore()


def test_get_unsat_core_and_proof(tm, solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-proofs", "true");

    uSort = solver.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
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

    unsat_core = solver.getUnsatCore()

    solver.getProof()
    solver.getProof(ProofComponent.SAT)

    solver.resetAssertions()
    for t in unsat_core:
        solver.assertFormula(t)
    res = solver.checkSat()
    assert res.isUnsat()
    solver.getProof()


def test_get_unsat_core_and_proof_to_string(tm, solver):
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

    proofs = solver.getProof()
    assert len(proofs) > 0
    printedProof = solver.proofToString(proofs[0])
    assert len(printedProof) > 0
    printedProof = solver.proofToString(proofs[0], ProofFormat.ALETHE)
    assert len(printedProof) > 0

    proofs = solver.getProof(ProofComponent.SAT)
    printedProof = solver.proofToString(proofs[0], ProofFormat.NONE)
    assert len(printedProof) > 0

def test_learned_literals(solver):
    solver.setOption("produce-learned-literals", "true")
    with pytest.raises(RuntimeError):
        solver.getLearnedLiterals()
    solver.checkSat()
    solver.getLearnedLiterals()
    solver.getLearnedLiterals(LearnedLitType.PREPROCESS)

def test_learned_literals2(tm, solver):
    solver.setOption("produce-learned-literals", "true")
    intSort = tm.getIntegerSort()
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    zero = tm.mkInteger(0)
    ten = tm.mkInteger(10)
    f0 = tm.mkTerm(Kind.GEQ, x, ten)
    f1 = tm.mkTerm(
            Kind.OR,
            tm.mkTerm(Kind.GEQ, zero, x),
            tm.mkTerm(Kind.GEQ, y, zero))
    solver.assertFormula(f0)
    solver.assertFormula(f1)
    solver.checkSat()
    solver.getLearnedLiterals(LearnedLitType.INPUT)

def test_get_timeout_core_unsat(tm, solver):
  solver.setOption("timeout-core-timeout", "100")
  solver.setOption("produce-unsat-cores", "true")
  intSort = tm.getIntegerSort()
  x = tm.mkConst(intSort, "x")
  tt = tm.mkBoolean(True)
  hard = tm.mkTerm(Kind.EQUAL,
                       tm.mkTerm(Kind.MULT, x, x),
                       tm.mkInteger("501240912901901249014210220059591"))
  solver.assertFormula(tt)
  solver.assertFormula(hard)
  res = solver.getTimeoutCore()
  assert res[0].isUnknown()
  assert len(res[1]) == 1
  assert res[1][0] == hard

def test_get_timeout_core(tm, solver):
  solver.setOption("produce-unsat-cores", "true")
  ff = tm.mkBoolean(False)
  tt = tm.mkBoolean(True)
  solver.assertFormula(tt)
  solver.assertFormula(ff)
  solver.assertFormula(tt)
  res = solver.getTimeoutCore()
  assert res[0].isUnsat()
  assert len(res[1]) == 1
  assert res[1][0] == ff

def test_get_timeout_core_assuming(tm, solver):
  solver.setOption("produce-unsat-cores", "true")
  ff = tm.mkBoolean(False)
  tt = tm.mkBoolean(True)
  solver.assertFormula(tt)
  res = solver.getTimeoutCoreAssuming(ff, tt)
  assert res[0].isUnsat()
  assert len(res[1]) == 1
  assert res[1][0] == ff

def test_get_timeout_core_assuming_empty(solver):
  solver.setOption("produce-unsat-cores", "true")
  with pytest.raises(RuntimeError):
    res = solver.getTimeoutCoreAssuming()

def test_get_value1(tm, solver):
    solver.setOption("produce-models", "false")
    t = tm.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValue(t)


def test_get_value2(tm, solver):
    solver.setOption("produce-models", "true")
    t = tm.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValue(t)


def test_get_value3(tm, solver):
    solver.setOption("produce-models", "true")
    uSort = tm.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    uToIntSort = tm.mkFunctionSort(uSort, intSort)
    intPredSort = tm.mkFunctionSort(intSort, boolSort)

    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    z = tm.mkConst(uSort, "z")
    f = tm.mkConst(uToIntSort, "f")
    p = tm.mkConst(intPredSort, "p")
    zero = tm.mkInteger(0)
    one = tm.mkInteger(1)
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    summ = tm.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)

    solver.assertFormula(tm.mkTerm(Kind.LEQ, zero, f_x))
    solver.assertFormula(tm.mkTerm(Kind.LEQ, zero, f_y))
    solver.assertFormula(tm.mkTerm(Kind.LEQ, summ, one))
    solver.assertFormula(p_0.notTerm())
    solver.assertFormula(p_f_y)
    assert solver.checkSat().isSat()
    solver.getValue(x)
    solver.getValue(y)
    solver.getValue(z)
    solver.getValue(summ)
    solver.getValue(p_f_y)

    a = [solver.getValue(x), solver.getValue(y), solver.getValue(z)]
    b = solver.getValue([x,y,z])
    assert a == b

    with pytest.raises(RuntimeError):
        Solver(tm).getValue(x)

    slv = Solver(tm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    slv.getValue(x)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.getValue(tm.mkConst(tm.getBooleanSort(), "x"))


def test_declare_sep_heap(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    integer = tm.getIntegerSort()
    solver.declareSepHeap(integer, integer)
    # cannot declare separation logic heap more than once
    with pytest.raises(RuntimeError):
        solver.declareSepHeap(integer, integer)

    with pytest.raises(RuntimeError):
        # no logic set yet
        Solver(tm).declareSepHeap(tm.getIntegerSort(), tm.getIntegerSort())

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setLogic("ALL")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.declareSepHeap(integer, ttm.getRealSort())

    slv = Solver(ttm)
    slv.setLogic("ALL");
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.declareSepHeap(ttm.getBooleanSort(), integer)


# Helper function for test_get_separation_{heap,nil}_termX. Asserts and checks
# some simple separation logic constraints.
def checkSimpleSeparationConstraints(slv):
    tm = slv.getTermManager()
    integer = tm.getIntegerSort()
    # declare the separation heap
    slv.declareSepHeap(integer, integer)
    x = tm.mkConst(integer, "x")
    p = tm.mkConst(integer, "p")
    heap = tm.mkTerm(Kind.SEP_PTO, p, x)
    slv.assertFormula(heap)
    nil = tm.mkSepNil(integer)
    slv.assertFormula(nil.eqTerm(tm.mkInteger(5)))
    slv.checkSat()


def test_get_value_sep_heap_1(tm, solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_2(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "false")
    checkSimpleSeparationConstraints(solver)
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_3(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_4(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_5(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    checkSimpleSeparationConstraints(solver)
    solver.getValueSepHeap()


def test_get_value_sep_nil_1(tm, solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_2(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "false")
    checkSimpleSeparationConstraints(solver)
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_3(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_4(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_5(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    checkSimpleSeparationConstraints(solver)
    solver.getValueSepNil()


def test_push1(solver):
    solver.setOption("incremental", "true")
    solver.push(1)
    with pytest.raises(RuntimeError):
        solver.setOption("incremental", "false")
    with pytest.raises(RuntimeError):
        solver.setOption("incremental", "true")


def test_push2(solver):
    solver.setOption("incremental", "false")
    with pytest.raises(RuntimeError):
        solver.push(1)


def test_pop1(solver):
    solver.setOption("incremental", "false")
    with pytest.raises(RuntimeError):
        solver.pop(1)


def test_pop2(solver):
    solver.setOption("incremental", "true")
    with pytest.raises(RuntimeError):
        solver.pop(1)


def test_pop3(solver):
    solver.setOption("incremental", "true")
    solver.push(1)
    solver.pop(1)
    with pytest.raises(RuntimeError):
        solver.pop(1)

def test_block_model1(tm, solver):
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.blockModel(BlockModelsMode.LITERALS)

def test_block_model2(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    with pytest.raises(RuntimeError):
        solver.blockModel(BlockModelsMode.LITERALS)

def test_block_model3(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x");
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    solver.blockModel(BlockModelsMode.LITERALS)

def test_block_model_values1(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x");
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.blockModelValues([])
    solver.blockModelValues([tm.mkBoolean(False)])

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.blockModelValues([tm.mkFalse()])

def test_block_model_values2(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    solver.blockModelValues([x])

def test_block_model_values3(tm, solver):
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.blockModelValues([x])

def test_block_model_values4(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    with pytest.raises(RuntimeError):
        solver.blockModelValues([x])

def test_block_model_values5(tm, solver):
    solver.setOption("produce-models", "true")
    x = tm.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    solver.blockModelValues([x])

def test_get_instantiations(tm, solver):
    iSort = tm.getIntegerSort()
    boolSort = solver.getBooleanSort()
    p = solver.declareFun("p", [iSort], boolSort)
    x = tm.mkVar(iSort, "x")
    bvl = tm.mkTerm(Kind.VARIABLE_LIST, x)
    app = tm.mkTerm(Kind.APPLY_UF, p, x)
    q = tm.mkTerm(Kind.FORALL, bvl, app)
    solver.assertFormula(q)
    five = tm.mkInteger(5)
    app2 = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.APPLY_UF, p, five))
    solver.assertFormula(app2)
    with pytest.raises(RuntimeError):
        solver.getInstantiations()
    solver.checkSat()
    solver.getInstantiations()

def test_get_statistics(tm, solver):
    # do some array reasoning to make sure we have a double statistics
    s1 = tm.getIntegerSort()
    s2 = tm.mkArraySort(s1, s1)
    t1 = tm.mkConst(s1, "i")
    t2 = tm.mkVar(s2, "a")
    t3 = tm.mkTerm(Kind.SELECT, t2, t1)
    solver.checkSat()

    stats = solver.getStatistics()

    assert not stats['global::totalTime']['internal']
    assert not stats['global::totalTime']['default']
    assert stats['global::totalTime']['value'][-2:] == 'ms' # ends with 'ms'
    assert stats['resource::resourceUnitsUsed']['internal']
    assert not stats['resource::resourceUnitsUsed']['default']
    assert stats.get(True)['resource::resourceUnitsUsed']['internal']
    assert not stats.get(True)['resource::resourceUnitsUsed']['default']

    assert '' not in stats
    assert len([s for s in stats]) > 0

    for s in stats:
        if s[0] == 'theory::arrays::avgIndexListLength':
            assert s[1]['internal']
            assert s[1]['default']
            assert isnan(s[1]['value'])


def test_set_info(solver):
    with pytest.raises(RuntimeError):
        solver.setInfo("cvc5-lagic", "QF_BV")
    with pytest.raises(RuntimeError):
        solver.setInfo("cvc2-logic", "QF_BV")
    with pytest.raises(RuntimeError):
        solver.setInfo("cvc5-logic", "asdf")

    solver.setInfo("source", "asdf")
    solver.setInfo("category", "asdf")
    solver.setInfo("difficulty", "asdf")
    solver.setInfo("filename", "asdf")
    solver.setInfo("license", "asdf")
    solver.setInfo("name", "asdf")
    solver.setInfo("notes", "asdf")

    solver.setInfo("smt-lib-version", "2")
    solver.setInfo("smt-lib-version", "2.0")
    solver.setInfo("smt-lib-version", "2.5")
    solver.setInfo("smt-lib-version", "2.6")
    with pytest.raises(RuntimeError):
        solver.setInfo("smt-lib-version", ".0")

    solver.setInfo("status", "sat")
    solver.setInfo("status", "unsat")
    solver.setInfo("status", "unknown")
    with pytest.raises(RuntimeError):
        solver.setInfo("status", "asdf")


def test_simplify(tm, solver):
    bvSort = tm.mkBitVectorSort(32)
    uSort = tm.mkUninterpretedSort("u")
    funSort1 = tm.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = tm.mkFunctionSort(uSort, tm.getIntegerSort())
    consListSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", tm.getIntegerSort())
    cons.addSelectorSelf("tail")
    consListSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    consListSpec.addConstructor(nil)
    consListSort = tm.mkDatatypeSort(consListSpec)

    x = tm.mkConst(bvSort, "x")
    solver.simplify(x)
    a = tm.mkConst(bvSort, "a")
    solver.simplify(a)
    b = tm.mkConst(bvSort, "b")
    solver.simplify(b)
    x_eq_x = tm.mkTerm(Kind.EQUAL, x, x)
    solver.simplify(x_eq_x)
    assert tm.mkTrue() != x_eq_x
    assert tm.mkTrue() == solver.simplify(x_eq_x)
    x_eq_b = tm.mkTerm(Kind.EQUAL, x, b)
    solver.simplify(x_eq_b)
    assert tm.mkTrue() != x_eq_b
    assert tm.mkTrue() != solver.simplify(x_eq_b)
    slv = Solver(tm)
    slv.simplify(x)

    i1 = tm.mkConst(tm.getIntegerSort(), "i1")
    solver.simplify(i1)
    i2 = tm.mkTerm(Kind.MULT, i1, tm.mkInteger("23"))
    solver.simplify(i2)
    assert i1 != i2
    assert i1 != solver.simplify(i2)
    i3 = tm.mkTerm(Kind.ADD, i1, tm.mkInteger(0))
    solver.simplify(i3)
    assert i1 != i3
    assert i1 == solver.simplify(i3)

    consList = consListSort.getDatatype()
    dt1 = tm.mkTerm(
        Kind.APPLY_CONSTRUCTOR,
        consList.getConstructor("cons").getTerm(),
        tm.mkInteger(0),
        tm.mkTerm(
            Kind.APPLY_CONSTRUCTOR,
            consList.getConstructor("nil").getTerm()))
    solver.simplify(dt1)
    dt2 = tm.mkTerm(
      Kind.APPLY_SELECTOR,
      consList["cons"].getSelector("head").getTerm(),
      dt1)
    solver.simplify(dt2)

    b1 = tm.mkVar(bvSort, "b1")
    solver.simplify(b1)
    b2 = tm.mkVar(bvSort, "b1")
    solver.simplify(b2)
    b3 = tm.mkVar(uSort, "b3")
    solver.simplify(b3)
    v1 = tm.mkConst(bvSort, "v1")
    solver.simplify(v1)
    v2 = tm.mkConst(tm.getIntegerSort(), "v2")
    solver.simplify(v2)
    f1 = tm.mkConst(funSort1, "f1")
    solver.simplify(f1)
    f2 = tm.mkConst(funSort2, "f2")
    solver.simplify(f2)
    solver.defineFunsRec([f1, f2], [[b1, b2], [b3]], [v1, v2])
    solver.simplify(f1)
    solver.simplify(f2)

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.simplify(x)

def test_simplify_apply_subs(tm, solver):
    solver.setOption("incremental", "true")
    intSort = tm.getIntegerSort()
    x = tm.mkConst(intSort, "x")
    zero = tm.mkInteger(0)
    eq = tm.mkTerm(Kind.EQUAL, x, zero)
    solver.assertFormula(eq)
    solver.checkSat()

    assert solver.simplify(x, False) == x
    assert solver.simplify(x, True) == zero

def test_assert_formula(tm, solver):
    solver.assertFormula(tm.mkTrue())
    slv = Solver(tm)
    slv.assertFormula(tm.mkTrue())

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.assertFormula(tm.mkTrue())


def test_check_sat(solver):
    solver.setOption("incremental", "false")
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.checkSat()


def test_check_sat_assuming(tm, solver):
    solver.setOption("incremental", "false")
    solver.checkSatAssuming(tm.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(tm.mkTrue())
    slv = Solver(tm)
    slv.checkSatAssuming(tm.mkTrue())

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.checkSatAssuming(tm.mkTrue())


def test_check_sat_assuming1(tm, solver):
    boolSort = tm.getBooleanSort()
    x = tm.mkConst(boolSort, "x")
    y = tm.mkConst(boolSort, "y")
    z = tm.mkTerm(Kind.AND, x, y)
    solver.setOption("incremental", "true")
    solver.checkSatAssuming(tm.mkTrue())
    solver.checkSatAssuming(tm.mkTrue())
    solver.checkSatAssuming(z)
    slv = Solver(tm)
    slv.checkSatAssuming(tm.mkTrue())


def test_check_sat_assuming2(tm, solver):
    solver.setOption("incremental", "true")

    uSort = tm.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = tm.mkFunctionSort(uSort, intSort)
    intPredSort = tm.mkFunctionSort(intSort, boolSort)

    # Constants
    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    # Functions
    f = tm.mkConst(uToIntSort, "f")
    p = tm.mkConst(intPredSort, "p")
    # Values
    zero = tm.mkInteger(0)
    one = tm.mkInteger(1)
    # Terms
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    summ = tm.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)
    # Assertions
    assertions =\
        tm.mkTerm(Kind.AND,\
                      tm.mkTerm(Kind.LEQ, zero, f_x),  # 0 <= f(x)
                       tm.mkTerm(Kind.LEQ, zero, f_y),  # 0 <= f(y)
                       tm.mkTerm(Kind.LEQ, summ, one),  # f(x) + f(y) <= 1
                       p_0.notTerm(),                        # not p(0)
                       p_f_y                                 # p(f(y))
                      )

    solver.checkSatAssuming(tm.mkTrue())
    solver.assertFormula(assertions)
    solver.checkSatAssuming(tm.mkTerm(Kind.DISTINCT, x, y))
    solver.checkSatAssuming(
        tm.mkFalse(),
         tm.mkTerm(Kind.DISTINCT, x, y))
    slv = Solver(tm)
    slv.checkSatAssuming(tm.mkTrue())


def test_set_logic(tm, solver):
    solver.setLogic("AUFLIRA")
    with pytest.raises(RuntimeError):
        solver.setLogic("AF_BV")
    solver.assertFormula(tm.mkTrue())
    with pytest.raises(RuntimeError):
        solver.setLogic("AUFLIRA")

def test_is_logic_set(solver):
    assert solver.isLogicSet() == False
    solver.setLogic("QF_BV")
    assert solver.isLogicSet() == True

def test_get_logic(solver):
    with pytest.raises(RuntimeError):
        solver.getLogic()
    solver.setLogic("QF_BV")
    assert solver.getLogic() == "QF_BV"

def test_set_option(tm, solver):
    solver.setOption("bv-sat-solver", "minisat")
    with pytest.raises(RuntimeError):
        solver.setOption("bv-sat-solver", "1")
    solver.assertFormula(tm.mkTrue())
    with pytest.raises(RuntimeError):
        solver.setOption("bv-sat-solver", "minisat")


def test_reset_assertions(tm, solver):
    solver.setOption("incremental", "true")

    bvSort = tm.mkBitVectorSort(4)
    one = tm.mkBitVector(4, 1)
    x = tm.mkConst(bvSort, "x")
    ule = tm.mkTerm(Kind.BITVECTOR_ULE, x, one)
    srem = tm.mkTerm(Kind.BITVECTOR_SREM, one, x)
    solver.push(4)
    slt = tm.mkTerm(Kind.BITVECTOR_SLT, srem, one)
    solver.resetAssertions()
    solver.checkSatAssuming(slt, ule)

def test_declare_sygus_var(tm, solver):
    solver.setOption("sygus", "true")
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    funSort = tm.mkFunctionSort([intSort], boolSort)

    solver.declareSygusVar("", boolSort)
    solver.declareSygusVar("", funSort)
    solver.declareSygusVar("b", boolSort)
    with pytest.raises(RuntimeError):
        solver.declareSygusVar("", cvc5.Sort())
    with pytest.raises(RuntimeError):
        solver.declareSygusVar("a", cvc5.Sort())
    with pytest.raises(RuntimeError):
        Solver(tm).declareSygusVar("", boolSort)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("sygus", "true")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.declareSygusVar("", boolSort)


def test_mk_sygus_grammar(tm, solver):
    boolTerm = tm.mkBoolean(True)
    boolVar = tm.mkVar(solver.getBooleanSort())
    intVar = tm.mkVar(tm.getIntegerSort())

    solver.mkGrammar([], [intVar])
    solver.mkGrammar([boolVar], [intVar])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([], [])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([], [boolTerm])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([boolTerm], [intVar])
    slv = Solver(tm)
    boolVar2 = tm.mkVar(tm.getBooleanSort())
    intVar2 = tm.mkVar(tm.getIntegerSort())
    slv.mkGrammar([boolVar2], [intVar2])
    slv.mkGrammar([boolVar], [intVar2])
    slv.mkGrammar([boolVar2], [intVar])

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("sygus", "true")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    boolVar2 = ttm.mkVar(tm.getBooleanSort())
    intVar2 = ttm.mkVar(tm.getIntegerSort())
    slv.mkGrammar([boolVar2], [intVar2])
    slv.mkGrammar([boolVar], [intVar2])
    slv.mkGrammar([boolVar2], [intVar])


def test_add_sygus_constraint(tm, solver):
    solver.setOption("sygus", "true")
    boolTerm = tm.mkBoolean(True)
    intTerm = tm.mkInteger(1)

    solver.addSygusConstraint(boolTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusConstraint(intTerm)

    slv = Solver(tm)
    with pytest.raises(RuntimeError):
        slv.addSygusConstraint(boolTerm)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("sygus", "true")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusConstraint(boolTerm)


def test_get_sygus_constraints(tm, solver):
    solver.setOption("sygus", "true")
    true_term = tm.mkBoolean(True)
    false_term = tm.mkBoolean(False)
    solver.addSygusConstraint(true_term)
    solver.addSygusConstraint(false_term)
    constraints = [true_term, false_term]
    assert solver.getSygusConstraints() == constraints


def test_add_sygus_assume(tm, solver):
    solver.setOption("sygus", "true")
    boolTerm = tm.mkBoolean(False)
    intTerm = tm.mkInteger(1)
    solver.addSygusAssume(boolTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusAssume(intTerm)
    slv = Solver(tm)
    with pytest.raises(RuntimeError):
        slv.addSygusAssume(boolTerm)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("sygus", "true")
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusAssume(boolTerm)


def test_get_sygus_assumptions(tm, solver):
    solver.setOption("sygus", "true")
    true_term = tm.mkBoolean(True)
    false_term = tm.mkBoolean(False)
    solver.addSygusAssume(true_term)
    solver.addSygusAssume(false_term)
    assumptions = [true_term, false_term]
    assert solver.getSygusAssumptions() == assumptions


def test_add_sygus_inv_constraint(tm, solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()
    real = solver.getRealSort()

    intTerm = tm.mkInteger(1)

    inv = solver.declareFun("inv", [real], boolean)
    pre = solver.declareFun("pre", [real], boolean)
    trans = solver.declareFun("trans", [real, real], boolean)
    post = solver.declareFun("post", [real], boolean)

    inv1 = solver.declareFun("inv1", [real], real)

    trans1 = solver.declareFun("trans1", [boolean, real], boolean)
    trans2 = solver.declareFun("trans2", [real, boolean], boolean)
    trans3 = solver.declareFun("trans3", [real, real], real)

    solver.addSygusInvConstraint(inv, pre, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(intTerm, pre, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv1, pre, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, trans, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, intTerm, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, pre, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans1, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans2, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans3, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans, trans)
    slv = Solver(tm)
    slv.setOption("sygus", "true")
    boolean2 = tm.getBooleanSort()
    real2 = tm.getRealSort()
    inv22 = solver.declareFun("inv", [real2], boolean2)
    pre22 = solver.declareFun("pre", [real2], boolean2)
    trans22 = solver.declareFun("trans", [real2, real2], boolean2)
    post22 = solver.declareFun("post", [real2], boolean2)
    slv.addSygusInvConstraint(inv22, pre22, trans22, post22)
    slv.addSygusInvConstraint(inv, pre22, trans22, post22)
    slv.addSygusInvConstraint(inv22, pre, trans22, post22)
    slv.addSygusInvConstraint(inv22, pre22, trans, post22)
    slv.addSygusInvConstraint(inv22, pre22, trans22, post)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("sygus", "true")
    boolean2 = tm.getBooleanSort()
    real2 = tm.getRealSort()
    inv22 = slv.declareFun("inv", [real2], boolean2)
    pre22 = slv.declareFun("pre", [real2], boolean2)
    trans22 = slv.declareFun("trans", [real2, real2], boolean2)
    post22 = slv.declareFun("post", [real2], boolean2)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusInvConstraint(inv22, pre22, trans22, post22)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusInvConstraint(inv, pre22, trans22, post22)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusInvConstraint(inv22, pre, trans22, post22)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusInvConstraint(inv22, pre22, trans, post22)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.addSygusInvConstraint(inv22, pre22, trans22, post)


def test_check_synth(solver):
    with pytest.raises(RuntimeError):
        solver.checkSynth()
    solver.setOption("sygus", "true")
    solver.checkSynth()


def test_get_synth_solution(tm, solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "false")

    x = tm.mkBoolean(False)
    f = solver.synthFun("f", [], solver.getBooleanSort())

    with pytest.raises(RuntimeError):
        solver.getSynthSolution(f)

    res = solver.checkSynth()
    assert res.hasSolution()

    solver.getSynthSolution(f)
    solver.getSynthSolution(f)

    with pytest.raises(RuntimeError):
        solver.getSynthSolution(x)

    slv = Solver(tm)
    with pytest.raises(RuntimeError):
        slv.getSynthSolution(f)


def test_check_synth_next(solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "true")
    f = solver.synthFun("f", [], solver.getBooleanSort())

    res = solver.checkSynth()
    assert res.hasSolution()
    solver.getSynthSolutions([f])

    res = solver.checkSynthNext()
    assert res.hasSolution()
    solver.getSynthSolutions([f])


def test_check_synth_next2(solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "false")
    f = solver.synthFun("f", [], solver.getBooleanSort())

    solver.checkSynth()
    with pytest.raises(RuntimeError):
        solver.checkSynthNext()


def test_check_synth_next3(solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "true")
    f = solver.synthFun("f", [], solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.checkSynthNext()


def test_find_synth(tm, solver):
    solver.setOption("sygus", "true")
    boolSort = solver.getBooleanSort()
    start = tm.mkVar(boolSort)
    g = solver.mkGrammar([], [start])
    truen = tm.mkBoolean(True)
    falsen = tm.mkBoolean(False)
    g.addRule(start, truen)
    g.addRule(start, falsen)
    f = solver.synthFun("f", [], solver.getBooleanSort(), g)

    # should enumerate based on the grammar of the function to synthesize above
    t = solver.findSynth(FindSynthTarget.ENUM)
    assert not t.isNull() and t.getSort().isBoolean()


def test_find_synth2(tm, solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "true")
    boolSort = solver.getBooleanSort()
    start = tm.mkVar(boolSort)
    g = solver.mkGrammar([], [start])
    truen = tm.mkBoolean(True)
    falsen = tm.mkBoolean(False)
    g.addRule(start, truen)
    g.addRule(start, falsen)

    # should enumerate true/false
    t = solver.findSynth(FindSynthTarget.ENUM, g)
    assert not t.isNull() and t.getSort().isBoolean()
    t = solver.findSynthNext()
    assert not t.isNull() and t.getSort().isBoolean()


def test_get_abduct(tm, solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-abducts", "true")
    solver.setOption("incremental", "false")

    intSort = tm.getIntegerSort()
    zero = tm.mkInteger(0)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")

    solver.assertFormula(tm.mkTerm(Kind.GT, x, zero))
    conj = tm.mkTerm(Kind.GT, y, zero)
    output = solver.getAbduct(conj)
    assert not output.isNull() and output.getSort().isBoolean()

    boolean = solver.getBooleanSort()
    truen = tm.mkBoolean(True)
    start = tm.mkVar(boolean)
    g = solver.mkGrammar([], [start])
    conj2 = tm.mkTerm(Kind.GT, x, zero)
    g.addRule(start, truen)
    output2 = solver.getAbduct(conj2, g)
    assert output2 == truen

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-abducts", "true")
    xx = ttm.mkConst(intSort, "x")
    yy = ttm.mkConst(intSort, "y")
    zzero = ttm.mkInteger(0)
    sstart = ttm.mkVar(ttm.getBooleanSort())
    slv.assertFormula(
        ttm.mkTerm(Kind.GT, ttm.mkTerm(Kind.ADD, xx, yy), zzero))
    gg = slv.mkGrammar([], [sstart])
    gg.addRule(sstart, ttm.mkTrue())
    cconj2 = ttm.mkTerm(Kind.EQUAL, zzero, zzero)
    slv.getAbduct(cconj2, gg)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.getAbduct(conj2)
    slv.getAbduct(conj2, gg)
    slv.getAbduct(cconj2, g)


def test_get_abduct2(tm, solver):
    solver.setLogic("QF_LIA")
    solver.setOption("incremental", "false")
    intSort = tm.getIntegerSort()
    zero = tm.mkInteger(0)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    solver.assertFormula(tm.mkTerm(Kind.GT, x, zero))
    conj = tm.mkTerm(Kind.GT, y, zero)
    with pytest.raises(RuntimeError):
        solver.getAbduct(conj)


def test_get_abduct_next(tm, solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-abducts", "true")
    solver.setOption("incremental", "true")

    intSort = tm.getIntegerSort()
    zero = tm.mkInteger(0)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")

    solver.assertFormula(tm.mkTerm(Kind.GT, x, zero))
    conj = tm.mkTerm(Kind.GT, y, zero)
    output = solver.getAbduct(conj)
    output2 = solver.getAbductNext()
    assert output != output2


def test_get_interpolant(tm, solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-interpolants", "true")
    solver.setOption("incremental", "false")

    intSort = tm.getIntegerSort()
    zero = tm.mkInteger(0)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    z = tm.mkConst(intSort, "z")

    solver.assertFormula(tm.mkTerm(
        Kind.GT, tm.mkTerm(Kind.ADD, x, y), zero))
    solver.assertFormula(tm.mkTerm(Kind.LT, x, zero))
    conj = tm.mkTerm(
            Kind.OR,
            tm.mkTerm(Kind.GT, tm.mkTerm(Kind.ADD, y, z), zero),
            tm.mkTerm(Kind.LT, z, zero))
    output = solver.getInterpolant(conj)
    assert output.getSort().isBoolean()

    boolean = solver.getBooleanSort()
    truen = tm.mkBoolean(True)
    start = tm.mkVar(boolean)
    g = solver.mkGrammar([], [start])
    conj2 = tm.mkTerm(Kind.EQUAL, zero, zero)
    g.addRule(start, truen)
    output2 = solver.getInterpolant(conj2, g)
    assert output2 == truen

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-interpolants", "true")
    xx = ttm.mkConst(intSort, "x")
    yy = ttm.mkConst(intSort, "y")
    zzero = ttm.mkInteger(0)
    sstart = ttm.mkVar(ttm.getBooleanSort())
    slv.assertFormula(
        ttm.mkTerm(Kind.GT, ttm.mkTerm(Kind.ADD, xx, yy), zzero))
    gg = slv.mkGrammar([], [sstart])
    gg.addRule(sstart, ttm.mkTrue())
    cconj2 = ttm.mkTerm(Kind.EQUAL, zzero, zzero)
    slv.getInterpolant(cconj2, gg)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.getInterpolant(conj2)
    slv.getInterpolant(conj2, gg)
    slv.getInterpolant(cconj2, g)


def test_get_interpolant_next(tm, solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-interpolants", "true")
    solver.setOption("incremental", "true")

    intSort = tm.getIntegerSort()
    zero = tm.mkInteger(0)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    z = tm.mkConst(intSort, "z")

    solver.assertFormula(tm.mkTerm(
        Kind.GT, tm.mkTerm(Kind.ADD, x, y), zero))
    solver.assertFormula(tm.mkTerm(Kind.LT, x, zero))
    conj = tm.mkTerm(
            Kind.OR,
            tm.mkTerm(Kind.GT, tm.mkTerm(Kind.ADD, y, z), zero),
            tm.mkTerm(Kind.LT, z, zero))
    output = solver.getInterpolant(conj)
    output2 = solver.getInterpolantNext()

    assert output != output2


def test_declare_pool(tm, solver):
    intSort = tm.getIntegerSort()
    setSort = tm.mkSetSort(intSort)
    zero = tm.mkInteger(0)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    # declare a pool with initial value  0, x, y
    p = solver.declarePool("p", intSort, [zero, x, y])
    # pool should have the same sort
    assert p.getSort() == setSort

    ttm = TermManager()
    slv = Solver(ttm)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.declarePool(
      "p",
      tm.getIntegerSort(),
      [tm.mkInteger(0), tm.mkConst(intSort, "x"), tm.mkConst(intSort, "y")])
    slv.declarePool(
      "p",
      tm.getIntegerSort(),
      [tm.mkInteger(0), tm.mkConst(intSort, "x"), tm.mkConst(intSort, "y")])
    slv.declarePool(
      "p",
      tm.getIntegerSort(),
      [tm.mkInteger(0), tm.mkConst(intSort, "x"), tm.mkConst(intSort, "y")])
    slv.declarePool(
      "p",
      tm.getIntegerSort(),
      [tm.mkInteger(0), tm.mkConst(intSort, "x"), tm.mkConst(intSort, "y")])


def test_get_model_domain_elements(tm, solver):
    solver.setOption("produce-models", "true")
    uSort = tm.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    z = tm.mkConst(uSort, "z")
    f = tm.mkTerm(Kind.DISTINCT, x, y, z)
    solver.assertFormula(f)
    solver.checkSat()
    solver.getModelDomainElements(uSort)
    assert len(solver.getModelDomainElements(uSort)) >= 3
    with pytest.raises(RuntimeError):
        solver.getModelDomainElements(intSort)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.getModelDomainElements(tm.mkUninterpretedSort("u"))

def test_get_model_domain_elements2(tm, solver):
    solver.setOption("produce-models", "true")
    solver.setOption("finite-model-find", "true")
    uSort = tm.mkUninterpretedSort("u")
    x = tm.mkVar(uSort, "x")
    y = tm.mkVar(uSort, "y")
    eq = tm.mkTerm(Kind.EQUAL, x, y)
    bvl = tm.mkTerm(Kind.VARIABLE_LIST, x, y)
    f = tm.mkTerm(Kind.FORALL, bvl, eq)
    solver.assertFormula(f)
    solver.checkSat()
    solver.getModelDomainElements(uSort)
    assert len(solver.getModelDomainElements(uSort)) == 1


def test_get_synth_solutions(tm, solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "false")

    x = tm.mkBoolean(False)
    f = solver.synthFun("f", [], solver.getBooleanSort())

    with pytest.raises(RuntimeError):
        solver.getSynthSolutions([])
    with pytest.raises(RuntimeError):
        solver.getSynthSolutions([f])

    solver.checkSynth()

    solver.getSynthSolutions([f])
    solver.getSynthSolutions([f, f])

    with pytest.raises(RuntimeError):
        solver.getSynthSolutions([])
    with pytest.raises(RuntimeError):
        solver.getSynthSolutions([x])

    slv = Solver(tm)
    with pytest.raises(RuntimeError):
        slv.getSynthSolutions([x])


def test_get_value_sep_heap1(tm, solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap2(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "false")
    checkSimpleSeparationConstraints(solver)
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap3(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap4(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap5(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    checkSimpleSeparationConstraints(solver)
    solver.getValueSepHeap()


def test_get_value_sep_nil1(tm, solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil2(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "false")
    checkSimpleSeparationConstraints(solver)
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil3(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil4(tm, solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = tm.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil5(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    checkSimpleSeparationConstraints(solver)
    solver.getValueSepNil()


def test_is_model_core_symbol(tm, solver):
    solver.setOption("produce-models", "true")
    solver.setOption("model-cores", "simple")
    uSort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    z = tm.mkConst(uSort, "z")
    zero = tm.mkInteger(0)
    f = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.EQUAL, x, y))
    solver.assertFormula(f)
    solver.checkSat()
    assert solver.isModelCoreSymbol(x)
    assert solver.isModelCoreSymbol(y)
    assert not solver.isModelCoreSymbol(z)
    with pytest.raises(RuntimeError):
        solver.isModelCoreSymbol(zero)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.isModelCoreSymbol(tm.mkConst(uSort, "x"))


def test_get_model(tm, solver):
    solver.setOption("produce-models", "true")
    uSort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    z = tm.mkConst(uSort, "z")
    f = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.EQUAL, x, y))
    solver.assertFormula(f)
    solver.checkSat()
    sorts = [uSort]
    terms = [x, y]
    solver.getModel(sorts, terms)


def test_get_model2(tm):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)


def test_get_model3(tm, solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    solver.checkSat()
    solver.getModel(sorts, terms)
    integer = tm.getIntegerSort()
    sorts.append(integer)
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)


def test_issue5893(tm):
    bvsort4 = tm.mkBitVectorSort(4)
    bvsort8 = tm.mkBitVectorSort(8)
    arrsort = tm.mkArraySort(bvsort4, bvsort8)
    arr = tm.mkConst(arrsort, "arr")
    idx = tm.mkConst(bvsort4, "idx")
    ten = tm.mkBitVector(8, "10", 10)
    sel = tm.mkTerm(Kind.SELECT, arr, idx)
    distinct = tm.mkTerm(Kind.DISTINCT, sel, ten)
    distinct.getOp()


def test_issue7000(tm, solver):
    s1 = tm.getIntegerSort()
    s2 = tm.mkFunctionSort(s1, s1)
    s3 = solver.getRealSort()
    t4 = tm.mkPi()
    t7 = tm.mkConst(s3, "_x5")
    t37 = tm.mkConst(s2, "_x32")
    t59 = tm.mkConst(s2, "_x51")
    t72 = tm.mkTerm(Kind.EQUAL, t37, t59)
    t74 = tm.mkTerm(Kind.GT, t4, t7)
    query = tm.mkTerm(Kind.AND, t72, t74, t72, t72)
    # throws logic exception since logic is not higher order by default
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(query.notTerm())


def test_mk_sygus_var(tm, solver):
    solver.setOption("sygus", "true")
    boolSort = solver.getBooleanSort()
    intSort = tm.getIntegerSort()
    funSort = tm.mkFunctionSort(intSort, boolSort)

    solver.declareSygusVar("", boolSort)
    solver.declareSygusVar("", funSort)
    solver.declareSygusVar("b", boolSort)
    slv = Solver(tm)
    with pytest.raises(RuntimeError):
        slv.declareSygusVar("", boolSort)


def test_synth_fun(tm, solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()
    integer = tm.getIntegerSort()

    x = tm.mkVar(boolean)

    start1 = tm.mkVar(boolean)
    start2 = tm.mkVar(integer)

    g1 = solver.mkGrammar(x, [start1])
    g1.addRule(start1, tm.mkBoolean(False))

    g2 = solver.mkGrammar(x, [start2])
    g2.addRule(start2, tm.mkInteger(0))

    solver.synthFun("", [], boolean)
    solver.synthFun("f1", [x], boolean)
    solver.synthFun("f2", [x], boolean, g1)

    with pytest.raises(RuntimeError):
        solver.synthFun("f6", [x], boolean, g2)
    slv = Solver(tm)
    slv.setOption("sygus", "true")
    x2 = tm.mkVar(tm.getBooleanSort())
    slv.synthFun("f1", [x2], tm.getBooleanSort())
    slv.synthFun("", [], tm.getBooleanSort())
    slv.synthFun("f1", [x], tm.getBooleanSort())

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("sygus", "true")
    slv.checkSat()
    x2 = ttm.mkVar(ttm.getBooleanSort())
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.synthFun("f1", [x2], tm.getBooleanSort())
    slv.synthFun("", [], tm.getBooleanSort())
    slv.synthFun("f1", [x], ttm.getBooleanSort())


def test_tuple_project(tm, solver):
    elements = [\
        tm.mkBoolean(True), \
        tm.mkInteger(3),\
        tm.mkString("C"),\
        tm.mkTerm(Kind.SET_SINGLETON, tm.mkString("Z"))]

    tuple = tm.mkTuple(elements)

    indices1 = []
    indices2 = [0]
    indices3 = [0, 1]
    indices4 = [0, 0, 2, 2, 3, 3, 0]
    indices5 = [4]
    indices6 = [0, 4]

    tm.mkTerm(tm.mkOp(Kind.TUPLE_PROJECT, *indices1), tuple)

    tm.mkTerm(tm.mkOp(Kind.TUPLE_PROJECT, *indices2), tuple)

    tm.mkTerm(tm.mkOp(Kind.TUPLE_PROJECT, *indices3), tuple)

    tm.mkTerm(tm.mkOp(Kind.TUPLE_PROJECT, *indices4), tuple)

    with pytest.raises(RuntimeError):
        tm.mkTerm(tm.mkOp(Kind.TUPLE_PROJECT, *indices5), tuple)
    with pytest.raises(RuntimeError):
        tm.mkTerm(tm.mkOp(Kind.TUPLE_PROJECT, *indices6), tuple)

    indices = [0, 3, 2, 0, 1, 2]

    op = tm.mkOp(Kind.TUPLE_PROJECT, *indices)
    projection = tm.mkTerm(op, tuple)

    datatype = tuple.getSort().getDatatype()
    constructor = datatype[0]

    for i in indices:

        selectorTerm = constructor[i].getTerm()
        selectedTerm = tm.mkTerm(Kind.APPLY_SELECTOR, selectorTerm, tuple)
        simplifiedTerm = solver.simplify(selectedTerm)
        assert elements[i] == simplifiedTerm

        assert "((_ tuple.project 0 3 2 0 1 2) "\
               "(tuple true 3 \"C\" (set.singleton \"Z\")))" == \
               str(projection)


def test_get_data_type_arity(tm, solver):
  ctor1 = tm.mkDatatypeConstructorDecl("_x21")
  ctor2 = tm.mkDatatypeConstructorDecl("_x31")
  s3 = solver.declareDatatype("_x17", ctor1, ctor2)
  assert s3.getDatatypeArity() == 0


def test_get_unsat_core_lemmas1(tm, solver):
  solver.setOption("produce-unsat-cores", "true")
  solver.setOption("unsat-cores-mode", "sat-proof")
  # cannot ask before a check sat
  with pytest.raises(RuntimeError):
      solver.getUnsatCoreLemmas()

  solver.assertFormula(tm.mkFalse())
  assert solver.checkSat().isUnsat()
  solver.getUnsatCoreLemmas()


def test_get_unsat_core_lemmas2(tm, solver):
  solver.setOption("produce-unsat-cores", "true")
  solver.setOption("unsat-cores-mode", "sat-proof")
  uSort = tm.mkUninterpretedSort("u")
  intSort = tm.getIntegerSort()
  boolSort = solver.getBooleanSort()
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
  solver.getUnsatCoreLemmas()

def test_get_difficulty(solver):
  solver.setOption("produce-difficulty", "true")
  # cannot ask before a check sat
  with pytest.raises(RuntimeError):
      solver.getDifficulty()
  solver.checkSat()
  solver.getDifficulty()

def test_get_difficulty2(solver):
  solver.checkSat()
  with pytest.raises(RuntimeError):
  # option is not set
      solver.getDifficulty()

def test_get_difficulty3(tm, solver):
  solver.setOption("produce-difficulty", "true")
  intSort = tm.getIntegerSort()
  x = tm.mkConst(intSort, "x")
  zero = tm.mkInteger(0)
  ten = tm.mkInteger(10)
  f0 = tm.mkTerm(Kind.GEQ, x, ten)
  f1 = tm.mkTerm(Kind.GEQ, zero, x)
  solver.checkSat()
  dmap = solver.getDifficulty()
  # difficulty should map assertions to integer values
  for key, value in dmap.items():
    assert key == f0 or key == f1
    assert value.getKind() == Kind.CONST_INTEGER

def test_get_model(tm, solver):
    solver.setOption("produce-models", "true")
    uSort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    z = tm.mkConst(uSort, "z")
    f = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.EQUAL, x, y));
    solver.assertFormula(f)
    solver.checkSat()
    sorts = [uSort]
    terms = [x, y]
    solver.getModel(sorts, terms)

def test_get_model2(solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)

def test_get_model_3(tm, solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    solver.checkSat()
    solver.getModel(sorts, terms)
    integer = tm.getIntegerSort()
    sorts += [integer]
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)

def test_get_option_names(solver):
    names = solver.getOptionNames()
    assert len(names) > 100
    assert "verbose" in names
    assert "foobar" not in names

def test_get_quantifier_elimination(tm, solver):
    x = tm.mkVar(solver.getBooleanSort(), "x")
    forall = tm.mkTerm(
            Kind.FORALL,
            tm.mkTerm(Kind.VARIABLE_LIST, x),
            tm.mkTerm(Kind.OR, x, tm.mkTerm(Kind.NOT, x)))
    with pytest.raises(RuntimeError):
        solver.getQuantifierElimination(tm.mkBoolean(False))
    solver.getQuantifierElimination(forall)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    xx = tm.mkVar(tm.getBooleanSort(), "x")
    fforall = tm.mkTerm(
            Kind.FORALL,
            tm.mkTerm(Kind.VARIABLE_LIST, xx),
            tm.mkTerm(Kind.OR, xx, tm.mkTerm(Kind.NOT, xx)))
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    slv.getQuantifierElimination(fforall)


def test_get_quantifier_elimination_disjunct(tm, solver):
    x = tm.mkVar(solver.getBooleanSort(), "x")
    forall = tm.mkTerm(
            Kind.FORALL,
            tm.mkTerm(Kind.VARIABLE_LIST, x),
            tm.mkTerm(Kind.OR, x, tm.mkTerm(Kind.NOT, x)))
    with pytest.raises(RuntimeError):
        solver.getQuantifierEliminationDisjunct(tm.mkBoolean(False))
    solver.getQuantifierEliminationDisjunct(forall)

    ttm = TermManager()
    slv = Solver(ttm)
    slv.setOption("produce-models", "true")
    slv.checkSat()
    xx = tm.mkVar(tm.getBooleanSort(), "x")
    fforall = tm.mkTerm(
            Kind.FORALL,
            tm.mkTerm(Kind.VARIABLE_LIST, xx),
            tm.mkTerm(Kind.OR, xx, tm.mkTerm(Kind.NOT, xx)))
    slv.getQuantifierEliminationDisjunct(fforall)


def test_get_version(solver):
    print(solver.getVersion())

class PluginUnsat(Plugin):
    def __init__(self, tm):
        super().__init__(tm)
        self.tm = tm

    def check(self):
        lemmas = [self.tm.mkBoolean(False)]
        return lemmas

    def getName(self):
        return "PluginUnsat"

def test_plugin_unsat(tm, solver):
    p = PluginUnsat(tm)
    solver.addPlugin(p)
    assert solver.checkSat().isUnsat()


class PluginListen(Plugin):
    def __init__(self, tm):
        super().__init__(tm)
        self.has_seen_theory_lemma = False
        self.has_seen_sat_clause = False

    def notifySatClause(self, cl):
        super().notifySatClause(cl)
        self.has_seen_sat_clause = True

    def hasSeenSatClause(self):
        return self.has_seen_sat_clause

    def notifyTheoryLemma(self, lem):
        super().notifyTheoryLemma(lem)
        self.has_seen_theory_lemma = True

    def hasSeenTheoryLemma(self):
        return self.has_seen_theory_lemma

    def getName(self):
        return "PluginListen"

def test_plugin_listen(tm, solver):
    # NOTE: this shouldn't be necessary but ensures notifySatClause is called here.
    solver.setOption("plugin-notify-sat-clause-in-solve", "false")
    pl = PluginListen(tm)
    solver.addPlugin(pl)
    stringSort = tm.getStringSort()
    x = tm.mkConst(stringSort, "x")
    y = tm.mkConst(stringSort, "y")
    ctn1 = tm.mkTerm(Kind.STRING_CONTAINS, x, y)
    ctn2 = tm.mkTerm(Kind.STRING_CONTAINS, y, x)
    solver.assertFormula(tm.mkTerm(Kind.OR, ctn1, ctn2))
    lx = tm.mkTerm(Kind.STRING_LENGTH, x)
    ly = tm.mkTerm(Kind.STRING_LENGTH, y)
    lc = tm.mkTerm(Kind.GT, lx, ly)
    solver.assertFormula(lc)
    assert solver.checkSat().isSat()
    # above input formulas should induce a theory lemma and SAT clause learning
    assert pl.hasSeenTheoryLemma()
    assert pl.hasSeenSatClause()
