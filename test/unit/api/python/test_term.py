###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
from cvc5 import Kind, RoundingMode
from cvc5 import Sort, Term
from fractions import Fraction


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_eq(solver):
    uSort = solver.mkUninterpretedSort("u")
    x = solver.mkVar(uSort, "x")
    y = solver.mkVar(uSort, "y")
    z = Term(solver)

    assert x == x
    assert not x != x
    assert not x == y
    assert x != y
    assert not (x == z)
    assert x != z


def test_get_id(solver):
    n = Term(solver)
    with pytest.raises(RuntimeError):
        n.getId()
    x = solver.mkVar(solver.getIntegerSort(), "x")
    x.getId()
    y = x
    assert x.getId() == y.getId()

    z = solver.mkVar(solver.getIntegerSort(), "z")
    assert x.getId() != z.getId()


def test_get_kind(solver):
    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(uSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    n = Term(solver)
    with pytest.raises(RuntimeError):
        n.getKind()
    x = solver.mkVar(uSort, "x")
    x.getKind()
    y = solver.mkVar(uSort, "y")
    y.getKind()

    f = solver.mkVar(funSort1, "f")
    f.getKind()
    p = solver.mkVar(funSort2, "p")
    p.getKind()

    zero = solver.mkInteger(0)
    zero.getKind()

    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    f_x.getKind()
    f_y = solver.mkTerm(Kind.APPLY_UF, f, y)
    f_y.getKind()
    sum = solver.mkTerm(Kind.ADD, f_x, f_y)
    sum.getKind()
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.getKind()
    p_f_y = solver.mkTerm(Kind.APPLY_UF, p, f_y)
    p_f_y.getKind()

    # Sequence kinds do not exist internally, test that the API properly
    # converts them back.
    seqSort = solver.mkSequenceSort(intSort)
    s = solver.mkConst(seqSort, "s")
    ss = solver.mkTerm(Kind.SEQ_CONCAT, s, s)
    assert ss.getKind() == Kind.SEQ_CONCAT


def test_get_sort(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    n = Term(solver)
    with pytest.raises(RuntimeError):
        n.getSort()
    x = solver.mkVar(bvSort, "x")
    x.getSort()
    assert x.getSort() == bvSort
    y = solver.mkVar(bvSort, "y")
    y.getSort()
    assert y.getSort() == bvSort

    f = solver.mkVar(funSort1, "f")
    f.getSort()
    assert f.getSort() == funSort1
    p = solver.mkVar(funSort2, "p")
    p.getSort()
    assert p.getSort() == funSort2

    zero = solver.mkInteger(0)
    zero.getSort()
    assert zero.getSort() == intSort

    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    f_x.getSort()
    assert f_x.getSort() == intSort
    f_y = solver.mkTerm(Kind.APPLY_UF, f, y)
    f_y.getSort()
    assert f_y.getSort() == intSort
    sum = solver.mkTerm(Kind.ADD, f_x, f_y)
    sum.getSort()
    assert sum.getSort() == intSort
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.getSort()
    assert p_0.getSort() == boolSort
    p_f_y = solver.mkTerm(Kind.APPLY_UF, p, f_y)
    p_f_y.getSort()
    assert p_f_y.getSort() == boolSort


def test_get_op(solver):
    intsort = solver.getIntegerSort()
    bvsort = solver.mkBitVectorSort(8)
    arrsort = solver.mkArraySort(bvsort, intsort)
    funsort = solver.mkFunctionSort(intsort, bvsort)

    x = solver.mkConst(intsort, "x")
    a = solver.mkConst(arrsort, "a")
    b = solver.mkConst(bvsort, "b")

    assert not x.hasOp()
    with pytest.raises(RuntimeError):
        x.getOp()

    ab = solver.mkTerm(Kind.SELECT, a, b)
    ext = solver.mkOp(Kind.BITVECTOR_EXTRACT, 4, 0)
    extb = solver.mkTerm(ext, b)

    assert ab.hasOp()
    assert not ab.getOp().isIndexed()
    # can compare directly to a Kind (will invoke constructor)
    assert extb.hasOp()
    assert extb.getOp().isIndexed()
    assert extb.getOp() == ext

    f = solver.mkConst(funsort, "f")
    fx = solver.mkTerm(Kind.APPLY_UF, f, x)

    assert not f.hasOp()
    with pytest.raises(RuntimeError):
        f.getOp()
    assert fx.hasOp()
    children = [c for c in fx]
    # testing rebuild from op and children
    assert fx == solver.mkTerm(fx.getOp(), *children)

    # Test Datatypes Ops
    sort = solver.mkParamSort("T")
    listDecl = solver.mkDatatypeDecl("paramlist", [sort])
    cons = solver.mkDatatypeConstructorDecl("cons")
    nil = solver.mkDatatypeConstructorDecl("nil")
    cons.addSelector("head", sort)
    cons.addSelectorSelf("tail")
    listDecl.addConstructor(cons)
    listDecl.addConstructor(nil)
    listSort = solver.mkDatatypeSort(listDecl)
    intListSort = listSort.instantiate([solver.getIntegerSort()])
    c = solver.mkConst(intListSort, "c")
    list1 = listSort.getDatatype()
    # list datatype constructor and selector operator terms
    consOpTerm = list1.getConstructor("cons").getTerm()
    nilOpTerm = list1.getConstructor("nil").getTerm()
    headOpTerm = list1["cons"].getSelector("head").getTerm()
    tailOpTerm = list1["cons"].getSelector("tail").getTerm()

    nilTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, nilOpTerm)
    consTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, consOpTerm,
                             solver.mkInteger(0), nilTerm)
    headTerm = solver.mkTerm(Kind.APPLY_SELECTOR, headOpTerm, consTerm)
    tailTerm = solver.mkTerm(Kind.APPLY_SELECTOR, tailOpTerm, consTerm)

    assert nilTerm.hasOp()
    assert consTerm.hasOp()
    assert headTerm.hasOp()
    assert tailTerm.hasOp()

    # Test rebuilding
    children = [c for c in headTerm]
    assert headTerm == solver.mkTerm(headTerm.getOp(), *children)


def test_has_get_symbol(solver):
    n = Term(solver)
    t = solver.mkBoolean(True)
    c = solver.mkConst(solver.getBooleanSort(), "|\\|")

    with pytest.raises(RuntimeError):
        n.hasSymbol()
    assert not t.hasSymbol()
    assert c.hasSymbol()

    with pytest.raises(RuntimeError):
        n.getSymbol()
    with pytest.raises(RuntimeError):
        t.getSymbol()
    assert c.getSymbol() == "|\\|"


def test_is_null(solver):
    x = Term(solver)
    assert x.isNull()
    x = solver.mkVar(solver.mkBitVectorSort(4), "x")
    assert not x.isNull()


def test_not_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    with pytest.raises(RuntimeError):
        Term(solver).notTerm()
    b = solver.mkTrue()
    b.notTerm()
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.notTerm()
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.notTerm()
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.notTerm()
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.notTerm()
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.notTerm()
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.notTerm()
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.notTerm()
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.notTerm()


def test_and_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    b = solver.mkTrue()
    with pytest.raises(RuntimeError):
        Term(solver).andTerm(b)
    with pytest.raises(RuntimeError):
        b.andTerm(Term(solver))
    b.andTerm(b)
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.andTerm(b)
    with pytest.raises(RuntimeError):
        x.andTerm(x)
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.andTerm(b)
    with pytest.raises(RuntimeError):
        f.andTerm(x)
    with pytest.raises(RuntimeError):
        f.andTerm(f)
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.andTerm(b)
    with pytest.raises(RuntimeError):
        p.andTerm(x)
    with pytest.raises(RuntimeError):
        p.andTerm(f)
    with pytest.raises(RuntimeError):
        p.andTerm(p)
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.andTerm(b)
    with pytest.raises(RuntimeError):
        zero.andTerm(x)
    with pytest.raises(RuntimeError):
        zero.andTerm(f)
    with pytest.raises(RuntimeError):
        zero.andTerm(p)
    with pytest.raises(RuntimeError):
        zero.andTerm(zero)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.andTerm(b)
    with pytest.raises(RuntimeError):
        f_x.andTerm(x)
    with pytest.raises(RuntimeError):
        f_x.andTerm(f)
    with pytest.raises(RuntimeError):
        f_x.andTerm(p)
    with pytest.raises(RuntimeError):
        f_x.andTerm(zero)
    with pytest.raises(RuntimeError):
        f_x.andTerm(f_x)
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.andTerm(b)
    with pytest.raises(RuntimeError):
        sum.andTerm(x)
    with pytest.raises(RuntimeError):
        sum.andTerm(f)
    with pytest.raises(RuntimeError):
        sum.andTerm(p)
    with pytest.raises(RuntimeError):
        sum.andTerm(zero)
    with pytest.raises(RuntimeError):
        sum.andTerm(f_x)
    with pytest.raises(RuntimeError):
        sum.andTerm(sum)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.andTerm(b)
    with pytest.raises(RuntimeError):
        p_0.andTerm(x)
    with pytest.raises(RuntimeError):
        p_0.andTerm(f)
    with pytest.raises(RuntimeError):
        p_0.andTerm(p)
    with pytest.raises(RuntimeError):
        p_0.andTerm(zero)
    with pytest.raises(RuntimeError):
        p_0.andTerm(f_x)
    with pytest.raises(RuntimeError):
        p_0.andTerm(sum)
    p_0.andTerm(p_0)
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.andTerm(b)
    with pytest.raises(RuntimeError):
        p_f_x.andTerm(x)
    with pytest.raises(RuntimeError):
        p_f_x.andTerm(f)
    with pytest.raises(RuntimeError):
        p_f_x.andTerm(p)
    with pytest.raises(RuntimeError):
        p_f_x.andTerm(zero)
    with pytest.raises(RuntimeError):
        p_f_x.andTerm(f_x)
    with pytest.raises(RuntimeError):
        p_f_x.andTerm(sum)
    p_f_x.andTerm(p_0)
    p_f_x.andTerm(p_f_x)


def test_or_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    b = solver.mkTrue()
    with pytest.raises(RuntimeError):
        Term(solver).orTerm(b)
    with pytest.raises(RuntimeError):
        b.orTerm(Term(solver))
    b.orTerm(b)
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.orTerm(b)
    with pytest.raises(RuntimeError):
        x.orTerm(x)
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.orTerm(b)
    with pytest.raises(RuntimeError):
        f.orTerm(x)
    with pytest.raises(RuntimeError):
        f.orTerm(f)
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.orTerm(b)
    with pytest.raises(RuntimeError):
        p.orTerm(x)
    with pytest.raises(RuntimeError):
        p.orTerm(f)
    with pytest.raises(RuntimeError):
        p.orTerm(p)
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.orTerm(b)
    with pytest.raises(RuntimeError):
        zero.orTerm(x)
    with pytest.raises(RuntimeError):
        zero.orTerm(f)
    with pytest.raises(RuntimeError):
        zero.orTerm(p)
    with pytest.raises(RuntimeError):
        zero.orTerm(zero)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.orTerm(b)
    with pytest.raises(RuntimeError):
        f_x.orTerm(x)
    with pytest.raises(RuntimeError):
        f_x.orTerm(f)
    with pytest.raises(RuntimeError):
        f_x.orTerm(p)
    with pytest.raises(RuntimeError):
        f_x.orTerm(zero)
    with pytest.raises(RuntimeError):
        f_x.orTerm(f_x)
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.orTerm(b)
    with pytest.raises(RuntimeError):
        sum.orTerm(x)
    with pytest.raises(RuntimeError):
        sum.orTerm(f)
    with pytest.raises(RuntimeError):
        sum.orTerm(p)
    with pytest.raises(RuntimeError):
        sum.orTerm(zero)
    with pytest.raises(RuntimeError):
        sum.orTerm(f_x)
    with pytest.raises(RuntimeError):
        sum.orTerm(sum)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.orTerm(b)
    with pytest.raises(RuntimeError):
        p_0.orTerm(x)
    with pytest.raises(RuntimeError):
        p_0.orTerm(f)
    with pytest.raises(RuntimeError):
        p_0.orTerm(p)
    with pytest.raises(RuntimeError):
        p_0.orTerm(zero)
    with pytest.raises(RuntimeError):
        p_0.orTerm(f_x)
    with pytest.raises(RuntimeError):
        p_0.orTerm(sum)
    p_0.orTerm(p_0)
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.orTerm(b)
    with pytest.raises(RuntimeError):
        p_f_x.orTerm(x)
    with pytest.raises(RuntimeError):
        p_f_x.orTerm(f)
    with pytest.raises(RuntimeError):
        p_f_x.orTerm(p)
    with pytest.raises(RuntimeError):
        p_f_x.orTerm(zero)
    with pytest.raises(RuntimeError):
        p_f_x.orTerm(f_x)
    with pytest.raises(RuntimeError):
        p_f_x.orTerm(sum)
    p_f_x.orTerm(p_0)
    p_f_x.orTerm(p_f_x)


def test_xor_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    b = solver.mkTrue()
    with pytest.raises(RuntimeError):
        Term(solver).xorTerm(b)
    with pytest.raises(RuntimeError):
        b.xorTerm(Term(solver))
    b.xorTerm(b)
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.xorTerm(b)
    with pytest.raises(RuntimeError):
        x.xorTerm(x)
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.xorTerm(b)
    with pytest.raises(RuntimeError):
        f.xorTerm(x)
    with pytest.raises(RuntimeError):
        f.xorTerm(f)
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.xorTerm(b)
    with pytest.raises(RuntimeError):
        p.xorTerm(x)
    with pytest.raises(RuntimeError):
        p.xorTerm(f)
    with pytest.raises(RuntimeError):
        p.xorTerm(p)
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.xorTerm(b)
    with pytest.raises(RuntimeError):
        zero.xorTerm(x)
    with pytest.raises(RuntimeError):
        zero.xorTerm(f)
    with pytest.raises(RuntimeError):
        zero.xorTerm(p)
    with pytest.raises(RuntimeError):
        zero.xorTerm(zero)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.xorTerm(b)
    with pytest.raises(RuntimeError):
        f_x.xorTerm(x)
    with pytest.raises(RuntimeError):
        f_x.xorTerm(f)
    with pytest.raises(RuntimeError):
        f_x.xorTerm(p)
    with pytest.raises(RuntimeError):
        f_x.xorTerm(zero)
    with pytest.raises(RuntimeError):
        f_x.xorTerm(f_x)
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.xorTerm(b)
    with pytest.raises(RuntimeError):
        sum.xorTerm(x)
    with pytest.raises(RuntimeError):
        sum.xorTerm(f)
    with pytest.raises(RuntimeError):
        sum.xorTerm(p)
    with pytest.raises(RuntimeError):
        sum.xorTerm(zero)
    with pytest.raises(RuntimeError):
        sum.xorTerm(f_x)
    with pytest.raises(RuntimeError):
        sum.xorTerm(sum)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.xorTerm(b)
    with pytest.raises(RuntimeError):
        p_0.xorTerm(x)
    with pytest.raises(RuntimeError):
        p_0.xorTerm(f)
    with pytest.raises(RuntimeError):
        p_0.xorTerm(p)
    with pytest.raises(RuntimeError):
        p_0.xorTerm(zero)
    with pytest.raises(RuntimeError):
        p_0.xorTerm(f_x)
    with pytest.raises(RuntimeError):
        p_0.xorTerm(sum)
    p_0.xorTerm(p_0)
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.xorTerm(b)
    with pytest.raises(RuntimeError):
        p_f_x.xorTerm(x)
    with pytest.raises(RuntimeError):
        p_f_x.xorTerm(f)
    with pytest.raises(RuntimeError):
        p_f_x.xorTerm(p)
    with pytest.raises(RuntimeError):
        p_f_x.xorTerm(zero)
    with pytest.raises(RuntimeError):
        p_f_x.xorTerm(f_x)
    with pytest.raises(RuntimeError):
        p_f_x.xorTerm(sum)
    p_f_x.xorTerm(p_0)
    p_f_x.xorTerm(p_f_x)


def test_eq_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    b = solver.mkTrue()
    with pytest.raises(RuntimeError):
        Term(solver).eqTerm(b)
    with pytest.raises(RuntimeError):
        b.eqTerm(Term(solver))
    b.eqTerm(b)
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.eqTerm(b)
    x.eqTerm(x)
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.eqTerm(b)
    with pytest.raises(RuntimeError):
        f.eqTerm(x)
    f.eqTerm(f)
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.eqTerm(b)
    with pytest.raises(RuntimeError):
        p.eqTerm(x)
    with pytest.raises(RuntimeError):
        p.eqTerm(f)
    p.eqTerm(p)
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.eqTerm(b)
    with pytest.raises(RuntimeError):
        zero.eqTerm(x)
    with pytest.raises(RuntimeError):
        zero.eqTerm(f)
    with pytest.raises(RuntimeError):
        zero.eqTerm(p)
    zero.eqTerm(zero)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.eqTerm(b)
    with pytest.raises(RuntimeError):
        f_x.eqTerm(x)
    with pytest.raises(RuntimeError):
        f_x.eqTerm(f)
    with pytest.raises(RuntimeError):
        f_x.eqTerm(p)
    f_x.eqTerm(zero)
    f_x.eqTerm(f_x)
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.eqTerm(b)
    with pytest.raises(RuntimeError):
        sum.eqTerm(x)
    with pytest.raises(RuntimeError):
        sum.eqTerm(f)
    with pytest.raises(RuntimeError):
        sum.eqTerm(p)
    sum.eqTerm(zero)
    sum.eqTerm(f_x)
    sum.eqTerm(sum)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.eqTerm(b)
    with pytest.raises(RuntimeError):
        p_0.eqTerm(x)
    with pytest.raises(RuntimeError):
        p_0.eqTerm(f)
    with pytest.raises(RuntimeError):
        p_0.eqTerm(p)
    with pytest.raises(RuntimeError):
        p_0.eqTerm(zero)
    with pytest.raises(RuntimeError):
        p_0.eqTerm(f_x)
    with pytest.raises(RuntimeError):
        p_0.eqTerm(sum)
    p_0.eqTerm(p_0)
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.eqTerm(b)
    with pytest.raises(RuntimeError):
        p_f_x.eqTerm(x)
    with pytest.raises(RuntimeError):
        p_f_x.eqTerm(f)
    with pytest.raises(RuntimeError):
        p_f_x.eqTerm(p)
    with pytest.raises(RuntimeError):
        p_f_x.eqTerm(zero)
    with pytest.raises(RuntimeError):
        p_f_x.eqTerm(f_x)
    with pytest.raises(RuntimeError):
        p_f_x.eqTerm(sum)
    p_f_x.eqTerm(p_0)
    p_f_x.eqTerm(p_f_x)


def test_imp_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    b = solver.mkTrue()
    with pytest.raises(RuntimeError):
        Term(solver).impTerm(b)
    with pytest.raises(RuntimeError):
        b.impTerm(Term(solver))
    b.impTerm(b)
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.impTerm(b)
    with pytest.raises(RuntimeError):
        x.impTerm(x)
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.impTerm(b)
    with pytest.raises(RuntimeError):
        f.impTerm(x)
    with pytest.raises(RuntimeError):
        f.impTerm(f)
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.impTerm(b)
    with pytest.raises(RuntimeError):
        p.impTerm(x)
    with pytest.raises(RuntimeError):
        p.impTerm(f)
    with pytest.raises(RuntimeError):
        p.impTerm(p)
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.impTerm(b)
    with pytest.raises(RuntimeError):
        zero.impTerm(x)
    with pytest.raises(RuntimeError):
        zero.impTerm(f)
    with pytest.raises(RuntimeError):
        zero.impTerm(p)
    with pytest.raises(RuntimeError):
        zero.impTerm(zero)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.impTerm(b)
    with pytest.raises(RuntimeError):
        f_x.impTerm(x)
    with pytest.raises(RuntimeError):
        f_x.impTerm(f)
    with pytest.raises(RuntimeError):
        f_x.impTerm(p)
    with pytest.raises(RuntimeError):
        f_x.impTerm(zero)
    with pytest.raises(RuntimeError):
        f_x.impTerm(f_x)
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.impTerm(b)
    with pytest.raises(RuntimeError):
        sum.impTerm(x)
    with pytest.raises(RuntimeError):
        sum.impTerm(f)
    with pytest.raises(RuntimeError):
        sum.impTerm(p)
    with pytest.raises(RuntimeError):
        sum.impTerm(zero)
    with pytest.raises(RuntimeError):
        sum.impTerm(f_x)
    with pytest.raises(RuntimeError):
        sum.impTerm(sum)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.impTerm(b)
    with pytest.raises(RuntimeError):
        p_0.impTerm(x)
    with pytest.raises(RuntimeError):
        p_0.impTerm(f)
    with pytest.raises(RuntimeError):
        p_0.impTerm(p)
    with pytest.raises(RuntimeError):
        p_0.impTerm(zero)
    with pytest.raises(RuntimeError):
        p_0.impTerm(f_x)
    with pytest.raises(RuntimeError):
        p_0.impTerm(sum)
    p_0.impTerm(p_0)
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.impTerm(b)
    with pytest.raises(RuntimeError):
        p_f_x.impTerm(x)
    with pytest.raises(RuntimeError):
        p_f_x.impTerm(f)
    with pytest.raises(RuntimeError):
        p_f_x.impTerm(p)
    with pytest.raises(RuntimeError):
        p_f_x.impTerm(zero)
    with pytest.raises(RuntimeError):
        p_f_x.impTerm(f_x)
    with pytest.raises(RuntimeError):
        p_f_x.impTerm(sum)
    p_f_x.impTerm(p_0)
    p_f_x.impTerm(p_f_x)


def test_ite_term(solver):
    bvSort = solver.mkBitVectorSort(8)
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    funSort1 = solver.mkFunctionSort(bvSort, intSort)
    funSort2 = solver.mkFunctionSort(intSort, boolSort)

    b = solver.mkTrue()
    with pytest.raises(RuntimeError):
        Term(solver).iteTerm(b, b)
    with pytest.raises(RuntimeError):
        b.iteTerm(Term(solver), b)
    with pytest.raises(RuntimeError):
        b.iteTerm(b, Term(solver))
    b.iteTerm(b, b)
    x = solver.mkVar(solver.mkBitVectorSort(8), "x")
    b.iteTerm(x, x)
    b.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        b.iteTerm(x, b)
    with pytest.raises(RuntimeError):
        x.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        x.iteTerm(x, b)
    f = solver.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        x.iteTerm(b, x)
    p = solver.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        p.iteTerm(x, b)
    zero = solver.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        zero.iteTerm(x, b)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        f_x.iteTerm(b, x)
    sum = solver.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        sum.iteTerm(b, x)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.iteTerm(b, b)
    p_0.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        p_0.iteTerm(x, b)
    p_f_x = solver.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.iteTerm(b, b)
    p_f_x.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        p_f_x.iteTerm(x, b)


def test_term_assignment(solver):
    t1 = solver.mkInteger(1)
    t2 = t1
    t2 = solver.mkInteger(2)
    assert t1 == solver.mkInteger(1)


def test_substitute(solver):
    x = solver.mkConst(solver.getIntegerSort(), "x")
    one = solver.mkInteger(1)
    ttrue = solver.mkTrue()
    xpx = solver.mkTerm(Kind.ADD, x, x)
    onepone = solver.mkTerm(Kind.ADD, one, one)

    assert xpx.substitute(x, one) == onepone
    assert onepone.substitute(one, x) == xpx
    # incorrect due to type
    with pytest.raises(RuntimeError):
        xpx.substitute(one, ttrue)

    # simultaneous substitution
    y = solver.mkConst(solver.getIntegerSort(), "y")
    xpy = solver.mkTerm(Kind.ADD, x, y)
    xpone = solver.mkTerm(Kind.ADD, y, one)
    es = []
    rs = []
    es.append(x)
    rs.append(y)
    es.append(y)
    rs.append(one)
    assert xpy.substitute(es, rs) == xpone

    # incorrect substitution due to arity
    rs.pop()
    with pytest.raises(RuntimeError):
        xpy.substitute(es, rs)

    # incorrect substitution due to types
    rs.append(ttrue)
    with pytest.raises(RuntimeError):
        xpy.substitute(es, rs)

    # null cannot substitute
    tnull = Term(solver)
    with pytest.raises(RuntimeError):
        tnull.substitute(one, x)
    with pytest.raises(RuntimeError):
        xpx.substitute(tnull, x)
    with pytest.raises(RuntimeError):
        xpx.substitute(x, tnull)
    rs.pop()
    rs.append(tnull)
    with pytest.raises(RuntimeError):
        xpy.substitute(es, rs)
    es.clear()
    rs.clear()
    es.append(x)
    rs.append(y)
    with pytest.raises(RuntimeError):
        tnull.substitute(es, rs)
    es.append(tnull)
    rs.append(one)
    with pytest.raises(RuntimeError):
        xpx.substitute(es, rs)


def test_term_compare(solver):
    t1 = solver.mkInteger(1)
    t2 = solver.mkTerm(Kind.ADD, solver.mkInteger(2), solver.mkInteger(2))
    t3 = solver.mkTerm(Kind.ADD, solver.mkInteger(2), solver.mkInteger(2))
    assert t2 >= t3
    assert t2 <= t3
    assert (t1 > t2) != (t1 < t2)
    assert (t1 > t2 or t1 == t2) == (t1 >= t2)


def test_term_children(solver):
    # simple term 2+3
    two = solver.mkInteger(2)
    t1 = solver.mkTerm(Kind.ADD, two, solver.mkInteger(3))
    assert t1[0] == two
    assert t1.getNumChildren() == 2
    tnull = Term(solver)
    with pytest.raises(RuntimeError):
        tnull.getNumChildren()

    # apply term f(2)
    intSort = solver.getIntegerSort()
    fsort = solver.mkFunctionSort(intSort, intSort)
    f = solver.mkConst(fsort, "f")
    t2 = solver.mkTerm(Kind.APPLY_UF, f, two)
    # due to our higher-order view of terms, we treat f as a child of
    # Kind.APPLY_UF
    assert t2.getNumChildren() == 2
    assert t2[0] == f
    assert t2[1] == two
    with pytest.raises(RuntimeError):
        tnull[0]


def test_get_const_array_base(solver):
    intsort = solver.getIntegerSort()
    arrsort = solver.mkArraySort(intsort, intsort)
    one = solver.mkInteger(1)
    constarr = solver.mkConstArray(arrsort, one)

    assert constarr.isConstArray()
    assert one == constarr.getConstArrayBase()

    with pytest.raises(RuntimeError):
        one.getConstArrayBase()

    a = solver.mkConst(arrsort, "a")
    with pytest.raises(RuntimeError):
        a.getConstArrayBase()


def test_get_uninterpreted_sort_value(solver):
    solver.setOption("produce-models", "true")
    uSort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    solver.assertFormula(solver.mkTerm(Kind.EQUAL, x, y))
    assert solver.checkSat().isSat()
    vx = solver.getValue(x)
    vy = solver.getValue(y)
    assert vx.isUninterpretedSortValue()
    assert vy.isUninterpretedSortValue()
    assert vx.getUninterpretedSortValue() == vy.getUninterpretedSortValue()


def test_is_rounding_mode_value(solver):
    assert not solver.mkInteger(15).isRoundingModeValue()
    assert solver.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).isRoundingModeValue()
    assert not solver.mkConst(
        solver.getRoundingModeSort()).isRoundingModeValue()


def test_get_rounding_mode_value(solver):
    with pytest.raises(RuntimeError):
        solver.mkInteger(15).getRoundingModeValue()
    assert solver.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).getRoundingModeValue(
        ) == RoundingMode.ROUND_NEAREST_TIES_TO_EVEN
    assert solver.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_POSITIVE).getRoundingModeValue(
        ) == RoundingMode.ROUND_TOWARD_POSITIVE
    assert solver.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_NEGATIVE).getRoundingModeValue(
        ) == RoundingMode.ROUND_TOWARD_NEGATIVE
    assert solver.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_ZERO).getRoundingModeValue(
        ) == RoundingMode.ROUND_TOWARD_ZERO
    assert solver.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).getRoundingModeValue(
        ) == RoundingMode.ROUND_NEAREST_TIES_TO_AWAY


def test_get_tuple(solver):
    t1 = solver.mkInteger(15)
    t2 = solver.mkReal(17, 25)
    t3 = solver.mkString("abc")

    tup = solver.mkTuple([t1, t2, t3])

    assert tup.isTupleValue()
    assert [t1, t2, t3] == tup.getTupleValue()


def test_get_set(solver):
    s = solver.mkSetSort(solver.getIntegerSort())

    i1 = solver.mkInteger(5)
    i2 = solver.mkInteger(7)

    s1 = solver.mkEmptySet(s)
    s2 = solver.mkTerm(Kind.SET_SINGLETON, i1)
    s3 = solver.mkTerm(Kind.SET_SINGLETON, i1)
    s4 = solver.mkTerm(Kind.SET_SINGLETON, i2)
    s5 = solver.mkTerm(
            Kind.SET_UNION, s2, solver.mkTerm(Kind.SET_UNION, s3, s4))

    assert s1.isSetValue()
    assert s2.isSetValue()
    assert s3.isSetValue()
    assert s4.isSetValue()
    assert not s5.isSetValue()
    s5 = solver.simplify(s5)
    assert s5.isSetValue()

    assert set([]) == s1.getSetValue()
    assert set([i1]) == s2.getSetValue()
    assert set([i1]) == s3.getSetValue()
    assert set([i2]) == s4.getSetValue()
    assert set([i1, i2]) == s5.getSetValue()


def test_get_sequence(solver):
    s = solver.mkSequenceSort(solver.getIntegerSort())

    i1 = solver.mkInteger(5)
    i2 = solver.mkInteger(7)

    s1 = solver.mkEmptySequence(s)
    s2 = solver.mkTerm(Kind.SEQ_UNIT, i1)
    s3 = solver.mkTerm(Kind.SEQ_UNIT, i1)
    s4 = solver.mkTerm(Kind.SEQ_UNIT, i2)
    s5 = solver.mkTerm(Kind.SEQ_CONCAT, s2,
                       solver.mkTerm(Kind.SEQ_CONCAT, s3, s4))

    assert s1.isSequenceValue()
    assert not s2.isSequenceValue()
    assert not s3.isSequenceValue()
    assert not s4.isSequenceValue()
    assert not s5.isSequenceValue()

    s2 = solver.simplify(s2)
    s3 = solver.simplify(s3)
    s4 = solver.simplify(s4)
    s5 = solver.simplify(s5)

    assert [] == s1.getSequenceValue()
    assert [i1] == s2.getSequenceValue()
    assert [i1] == s3.getSequenceValue()
    assert [i2] == s4.getSequenceValue()
    assert [i1, i1, i2] == s5.getSequenceValue()


def test_get_floating_point(solver):
    bvval = solver.mkBitVector(16, "0000110000000011", 2)
    fp = solver.mkFloatingPoint(5, 11, bvval)

    assert fp.isFloatingPointValue()
    assert not fp.isFloatingPointPosZero()
    assert not fp.isFloatingPointNegZero()
    assert not fp.isFloatingPointPosInf()
    assert not fp.isFloatingPointNegInf()
    assert not fp.isFloatingPointNaN()
    assert (5, 11, bvval) == fp.getFloatingPointValue()

    assert solver.mkFloatingPointPosZero(5, 11).isFloatingPointPosZero()
    assert solver.mkFloatingPointNegZero(5, 11).isFloatingPointNegZero()
    assert solver.mkFloatingPointPosInf(5, 11).isFloatingPointPosInf()
    assert solver.mkFloatingPointNegInf(5, 11).isFloatingPointNegInf()
    assert solver.mkFloatingPointNaN(5, 11).isFloatingPointNaN()


def test_is_integer(solver):
    int1 = solver.mkInteger("-18446744073709551616")
    int2 = solver.mkInteger("-18446744073709551615")
    int3 = solver.mkInteger("-4294967296")
    int4 = solver.mkInteger("-4294967295")
    int5 = solver.mkInteger("-10")
    int6 = solver.mkInteger("0")
    int7 = solver.mkInteger("10")
    int8 = solver.mkInteger("4294967295")
    int9 = solver.mkInteger("4294967296")
    int10 = solver.mkInteger("18446744073709551615")
    int11 = solver.mkInteger("18446744073709551616")
    int12 = solver.mkInteger("-0")

    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("-")
    with pytest.raises(RuntimeError):
        solver.mkInteger("-1-")
    with pytest.raises(RuntimeError):
        solver.mkInteger("0.0")
    with pytest.raises(RuntimeError):
        solver.mkInteger("-0.1")
    with pytest.raises(RuntimeError):
        solver.mkInteger("012")
    with pytest.raises(RuntimeError):
        solver.mkInteger("0000")
    with pytest.raises(RuntimeError):
        solver.mkInteger("-01")
    with pytest.raises(RuntimeError):
        solver.mkInteger("-00")

    assert int1.isIntegerValue()
    assert int2.isIntegerValue()
    assert int3.isIntegerValue()
    assert int4.isIntegerValue()
    assert int5.isIntegerValue()
    assert int6.isIntegerValue()
    assert int7.isIntegerValue()
    assert int8.isIntegerValue()
    assert int9.isIntegerValue()
    assert int10.isIntegerValue()
    assert int11.isIntegerValue()

    assert int1.getIntegerValue() == -18446744073709551616
    assert int2.getIntegerValue() == -18446744073709551615
    assert int3.getIntegerValue() == -4294967296
    assert int4.getIntegerValue() == -4294967295
    assert int5.getIntegerValue() == -10
    assert int6.getIntegerValue() == 0
    assert int7.getIntegerValue() == 10
    assert int8.getIntegerValue() == 4294967295
    assert int9.getIntegerValue() == 4294967296
    assert int10.getIntegerValue() == 18446744073709551615
    assert int11.getIntegerValue() == 18446744073709551616
    
    assert int1.getRealOrIntegerValueSign() == -1
    assert int6.getRealOrIntegerValueSign() == 0
    assert int7.getRealOrIntegerValueSign() == 1


def test_get_string(solver):
    s1 = solver.mkString("abcde")
    assert s1.isStringValue()
    assert s1.getStringValue() == str("abcde")


def test_get_real(solver):
    real1 = solver.mkReal("0")
    real2 = solver.mkReal(".0")
    real3 = solver.mkReal("-17")
    real4 = solver.mkReal("-3/5")
    real5 = solver.mkReal("12.7")
    real6 = solver.mkReal("1/4294967297")
    real7 = solver.mkReal("4294967297")
    real8 = solver.mkReal("1/18446744073709551617")
    real9 = solver.mkReal("18446744073709551617")

    assert real1.isRealValue()
    assert real2.isRealValue()
    assert real3.isRealValue()
    assert real4.isRealValue()
    assert real5.isRealValue()
    assert real6.isRealValue()
    assert real7.isRealValue()
    assert real8.isRealValue()
    assert real9.isRealValue()

    assert 0 == real1.getRealValue()
    assert 0 == real2.getRealValue()
    assert -17 == real3.getRealValue()
    assert Fraction(-3, 5) == real4.getRealValue()
    assert Fraction(127, 10) == real5.getRealValue()
    assert Fraction(1, 4294967297) == real6.getRealValue()
    assert 4294967297 == real7.getRealValue()
    assert Fraction(1, 18446744073709551617) == real8.getRealValue()
    assert Fraction(18446744073709551617, 1) == real9.getRealValue()

    # Check denominator too large for float
    num = 1
    den = 2 ** 64 + 1
    real_big = solver.mkReal(num, den)
    assert real_big.isRealValue()
    assert Fraction(num, den) == real_big.getRealValue()

    # Check that we're treating floats as decimal aproximations rather than
    # IEEE-754-specified values.
    real_decimal = solver.mkReal(0.3)
    assert real_decimal.isRealValue()
    assert Fraction("0.3") == real_decimal.getRealValue()
    assert Fraction(0.3) == Fraction(5404319552844595, 18014398509481984)
    assert Fraction(0.3) != real_decimal.getRealValue()


def test_get_boolean(solver):
    b1 = solver.mkBoolean(True)
    b2 = solver.mkBoolean(False)

    assert b1.isBooleanValue()
    assert b2.isBooleanValue()
    assert b1.getBooleanValue()
    assert not b2.getBooleanValue()


def test_get_bit_vector(solver):
    b1 = solver.mkBitVector(8, 15)
    b2 = solver.mkBitVector(8, "00001111", 2)
    b3 = solver.mkBitVector(8, "15", 10)
    b4 = solver.mkBitVector(8, "0f", 16)
    b5 = solver.mkBitVector(9, "00001111", 2);
    b6 = solver.mkBitVector(9, "15", 10);
    b7 = solver.mkBitVector(9, "0f", 16);

    assert b1.isBitVectorValue()
    assert b2.isBitVectorValue()
    assert b3.isBitVectorValue()
    assert b4.isBitVectorValue()
    assert b5.isBitVectorValue()
    assert b6.isBitVectorValue()
    assert b7.isBitVectorValue()

    assert "00001111" == b1.getBitVectorValue(2)
    assert "15" == b1.getBitVectorValue(10)
    assert "f" == b1.getBitVectorValue(16)
    assert "00001111" == b2.getBitVectorValue(2)
    assert "15" == b2.getBitVectorValue(10)
    assert "f" == b2.getBitVectorValue(16)
    assert "00001111" == b3.getBitVectorValue(2)
    assert "15" == b3.getBitVectorValue(10)
    assert "f" == b3.getBitVectorValue(16)
    assert "00001111" == b4.getBitVectorValue(2)
    assert "15" == b4.getBitVectorValue(10)
    assert "f" == b4.getBitVectorValue(16)
    assert "000001111" == b5.getBitVectorValue(2)
    assert "15" == b5.getBitVectorValue(10)
    assert "f" == b5.getBitVectorValue(16)
    assert "000001111" == b6.getBitVectorValue(2)
    assert "15" == b6.getBitVectorValue(10)
    assert "f" == b6.getBitVectorValue(16)
    assert "000001111" == b7.getBitVectorValue(2)
    assert "15" == b7.getBitVectorValue(10)
    assert "f" == b7.getBitVectorValue(16)


def test_const_array(solver):
    intsort = solver.getIntegerSort()
    arrsort = solver.mkArraySort(intsort, intsort)
    a = solver.mkConst(arrsort, "a")
    one = solver.mkInteger(1)
    two = solver.mkBitVector(2, 2)
    iconst = solver.mkConst(intsort)
    constarr = solver.mkConstArray(arrsort, one)

    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrsort, two)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrsort, iconst)

    assert constarr.getKind() == Kind.CONST_ARRAY
    assert constarr.getConstArrayBase() == one
    with pytest.raises(RuntimeError):
        a.getConstArrayBase()

    arrsort = solver.mkArraySort(solver.getRealSort(), solver.getRealSort())
    zero_array = solver.mkConstArray(arrsort, solver.mkReal(0))
    stores = solver.mkTerm(Kind.STORE, zero_array, solver.mkReal(1),
                           solver.mkReal(2))
    stores = solver.mkTerm(Kind.STORE, stores, solver.mkReal(2),
                           solver.mkReal(3))
    stores = solver.mkTerm(Kind.STORE, stores, solver.mkReal(4),
                           solver.mkReal(5))


def test_const_sequence_elements(solver):
    realsort = solver.getRealSort()
    seqsort = solver.mkSequenceSort(realsort)
    s = solver.mkEmptySequence(seqsort)

    assert s.getKind() == Kind.CONST_SEQUENCE
    # empty sequence has zero elements
    cs = s.getSequenceValue()
    assert len(cs) == 0

    # A seq.unit app is not a constant sequence (regardless of whether it is
    # applied to a constant).
    su = solver.mkTerm(Kind.SEQ_UNIT, solver.mkReal(1))
    with pytest.raises(RuntimeError):
        su.getSequenceValue()

def test_get_cardinality_constraint(solver):
  su = solver.mkUninterpretedSort("u")
  t = solver.mkCardinalityConstraint(su, 3)
  assert t.isCardinalityConstraint()
  cc = t.getCardinalityConstraint()
  assert cc[0] == su
  assert cc[1] == 3
  x = solver.mkConst(solver.getIntegerSort(), "x")
  assert not x.isCardinalityConstraint()
  with pytest.raises(RuntimeError):
    x.getCardinalityConstraint()
  nullt = cvc5.Term(solver)
  with pytest.raises(RuntimeError):
    nullt.isCardinalityConstraint()

def test_get_real_algebraic_number(solver):
  solver.setOption("produce-models", "true")
  solver.setLogic("QF_NRA")
  realsort = solver.getRealSort()
  x = solver.mkConst(realsort, "x")
  x2 = solver.mkTerm(Kind.MULT, x, x)
  two = solver.mkReal(2, 1)
  eq = solver.mkTerm(Kind.EQUAL, x2, two)
  solver.assertFormula(eq)
  # Note that check-sat should only return "sat" if libpoly is enabled.
  # Otherwise, we do not test the following functionality.
  if solver.checkSat().isSat():
    # We find a model for (x*x = 2), where x should be a real algebraic number.
    # We assert that its defining polynomial is non-null and its lower and
    # upper bounds are real.
    vx = solver.getValue(x)
    assert vx.isRealAlgebraicNumber()
    y = solver.mkVar(realsort, "y")
    poly = vx.getRealAlgebraicNumberDefiningPolynomial(y)
    assert not poly.isNull()
    lb = vx.getRealAlgebraicNumberLowerBound()
    assert lb.isRealValue()
    ub = vx.getRealAlgebraicNumberUpperBound()
    assert ub.isRealValue()

def test_term_scoped_to_string(solver):
    intsort = solver.getIntegerSort()
    x = solver.mkConst(intsort, "x")
    assert str(x) == "x"
    solver2 = cvc5.Solver()
    assert str(x) == "x"
