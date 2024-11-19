###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Andrew Reynolds
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
from cvc5 import Kind, RoundingMode
from cvc5 import Sort, Term
from fractions import Fraction


@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def test_eq(tm):
    uSort = tm.mkUninterpretedSort("u")
    x = tm.mkVar(uSort, "x")
    y = tm.mkVar(uSort, "y")
    assert x == x
    assert not x != x
    assert not x == y
    assert x != y


def test_get_id(tm):
    x = tm.mkVar(tm.getIntegerSort(), "x")
    x.getId()
    y = x
    assert x.getId() == y.getId()
    z = tm.mkVar(tm.getIntegerSort(), "z")
    assert x.getId() != z.getId()


def test_get_kind(tm):
    uSort = tm.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(uSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    x = tm.mkVar(uSort, "x")
    x.getKind()
    y = tm.mkVar(uSort, "y")
    y.getKind()

    f = tm.mkVar(funSort1, "f")
    f.getKind()
    p = tm.mkVar(funSort2, "p")
    p.getKind()

    zero = tm.mkInteger(0)
    zero.getKind()

    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_x.getKind()
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    f_y.getKind()
    sum = tm.mkTerm(Kind.ADD, f_x, f_y)
    sum.getKind()
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.getKind()
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)
    p_f_y.getKind()

    # Sequence kinds do not exist internally, test that the API properly
    # converts them back.
    seqSort = tm.mkSequenceSort(intSort)
    s = tm.mkConst(seqSort, "s")
    ss = tm.mkTerm(Kind.SEQ_CONCAT, s, s)
    assert ss.getKind() == Kind.SEQ_CONCAT


def test_get_sort(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    x = tm.mkVar(bvSort, "x")
    x.getSort()
    assert x.getSort() == bvSort
    y = tm.mkVar(bvSort, "y")
    y.getSort()
    assert y.getSort() == bvSort

    f = tm.mkVar(funSort1, "f")
    f.getSort()
    assert f.getSort() == funSort1
    p = tm.mkVar(funSort2, "p")
    p.getSort()
    assert p.getSort() == funSort2

    zero = tm.mkInteger(0)
    zero.getSort()
    assert zero.getSort() == intSort

    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_x.getSort()
    assert f_x.getSort() == intSort
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    f_y.getSort()
    assert f_y.getSort() == intSort
    sum = tm.mkTerm(Kind.ADD, f_x, f_y)
    sum.getSort()
    assert sum.getSort() == intSort
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.getSort()
    assert p_0.getSort() == boolSort
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)
    p_f_y.getSort()
    assert p_f_y.getSort() == boolSort


def test_get_op(tm):
    intsort = tm.getIntegerSort()
    bvsort = tm.mkBitVectorSort(8)
    arrsort = tm.mkArraySort(bvsort, intsort)
    funsort = tm.mkFunctionSort(intsort, bvsort)

    x = tm.mkConst(intsort, "x")
    a = tm.mkConst(arrsort, "a")
    b = tm.mkConst(bvsort, "b")

    assert not x.hasOp()
    with pytest.raises(RuntimeError):
        x.getOp()

    ab = tm.mkTerm(Kind.SELECT, a, b)
    ext = tm.mkOp(Kind.BITVECTOR_EXTRACT, 4, 0)
    extb = tm.mkTerm(ext, b)

    assert ab.hasOp()
    assert not ab.getOp().isIndexed()
    # can compare directly to a Kind (will invoke constructor)
    assert extb.hasOp()
    assert extb.getOp().isIndexed()
    assert extb.getOp() == ext

    bit = tm.mkOp(Kind.BITVECTOR_BIT, 4)
    bitb = tm.mkTerm(bit, b)
    assert bitb.getKind() == Kind.BITVECTOR_BIT
    assert bitb.hasOp()
    assert bitb.getOp() == bit
    assert bitb.getOp().isIndexed()
    assert bit.getNumIndices() == 1
    assert bit[0] == tm.mkInteger(4)

    f = tm.mkConst(funsort, "f")
    fx = tm.mkTerm(Kind.APPLY_UF, f, x)

    assert not f.hasOp()
    with pytest.raises(RuntimeError):
        f.getOp()
    assert fx.hasOp()
    children = [c for c in fx]
    # testing rebuild from op and children
    assert fx == tm.mkTerm(fx.getOp(), *children)

    # Test Datatypes Ops
    sort = tm.mkParamSort("T")
    listDecl = tm.mkDatatypeDecl("paramlist", [sort])
    cons = tm.mkDatatypeConstructorDecl("cons")
    nil = tm.mkDatatypeConstructorDecl("nil")
    cons.addSelector("head", sort)
    cons.addSelectorSelf("tail")
    listDecl.addConstructor(cons)
    listDecl.addConstructor(nil)
    listSort = tm.mkDatatypeSort(listDecl)
    intListSort = listSort.instantiate([tm.getIntegerSort()])
    c = tm.mkConst(intListSort, "c")
    list1 = listSort.getDatatype()
    # list datatype constructor and selector operator terms
    consOpTerm = list1.getConstructor("cons").getTerm()
    nilOpTerm = list1.getConstructor("nil").getTerm()
    headOpTerm = list1["cons"].getSelector("head").getTerm()
    tailOpTerm = list1["cons"].getSelector("tail").getTerm()

    nilTerm = tm.mkTerm(Kind.APPLY_CONSTRUCTOR, nilOpTerm)
    consTerm = tm.mkTerm(Kind.APPLY_CONSTRUCTOR, consOpTerm,
                             tm.mkInteger(0), nilTerm)
    headTerm = tm.mkTerm(Kind.APPLY_SELECTOR, headOpTerm, consTerm)
    tailTerm = tm.mkTerm(Kind.APPLY_SELECTOR, tailOpTerm, consTerm)

    assert nilTerm.hasOp()
    assert consTerm.hasOp()
    assert headTerm.hasOp()
    assert tailTerm.hasOp()

    # Test rebuilding
    children = [c for c in headTerm]
    assert headTerm == tm.mkTerm(headTerm.getOp(), *children)


def test_has_get_symbol(tm):
    t = tm.mkBoolean(True)
    c = tm.mkConst(tm.getBooleanSort(), "|\\|")

    assert not t.hasSymbol()
    assert c.hasSymbol()

    with pytest.raises(RuntimeError):
        t.getSymbol()
    assert c.getSymbol() == "|\\|"


def test_is_null(tm):
    x = tm.mkVar(tm.mkBitVectorSort(4), "x")
    assert not x.isNull()


def test_not_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.notTerm()
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.notTerm()
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.notTerm()
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.notTerm()
    zero = tm.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.notTerm()
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.notTerm()
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.notTerm()
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.notTerm()
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.notTerm()


def test_and_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.andTerm(b)
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.andTerm(b)
    with pytest.raises(RuntimeError):
        x.andTerm(x)
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.andTerm(b)
    with pytest.raises(RuntimeError):
        f.andTerm(x)
    with pytest.raises(RuntimeError):
        f.andTerm(f)
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.andTerm(b)
    with pytest.raises(RuntimeError):
        p.andTerm(x)
    with pytest.raises(RuntimeError):
        p.andTerm(f)
    with pytest.raises(RuntimeError):
        p.andTerm(p)
    zero = tm.mkInteger(0)
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
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
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
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
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
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
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
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
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


def test_or_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.orTerm(b)
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.orTerm(b)
    with pytest.raises(RuntimeError):
        x.orTerm(x)
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.orTerm(b)
    with pytest.raises(RuntimeError):
        f.orTerm(x)
    with pytest.raises(RuntimeError):
        f.orTerm(f)
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.orTerm(b)
    with pytest.raises(RuntimeError):
        p.orTerm(x)
    with pytest.raises(RuntimeError):
        p.orTerm(f)
    with pytest.raises(RuntimeError):
        p.orTerm(p)
    zero = tm.mkInteger(0)
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
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
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
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
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
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
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
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
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


def test_xor_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.xorTerm(b)
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.xorTerm(b)
    with pytest.raises(RuntimeError):
        x.xorTerm(x)
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.xorTerm(b)
    with pytest.raises(RuntimeError):
        f.xorTerm(x)
    with pytest.raises(RuntimeError):
        f.xorTerm(f)
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.xorTerm(b)
    with pytest.raises(RuntimeError):
        p.xorTerm(x)
    with pytest.raises(RuntimeError):
        p.xorTerm(f)
    with pytest.raises(RuntimeError):
        p.xorTerm(p)
    zero = tm.mkInteger(0)
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
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
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
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
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
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
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
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
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


def test_eq_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.eqTerm(b)
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.eqTerm(b)
    x.eqTerm(x)
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.eqTerm(b)
    with pytest.raises(RuntimeError):
        f.eqTerm(x)
    f.eqTerm(f)
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.eqTerm(b)
    with pytest.raises(RuntimeError):
        p.eqTerm(x)
    with pytest.raises(RuntimeError):
        p.eqTerm(f)
    p.eqTerm(p)
    zero = tm.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.eqTerm(b)
    with pytest.raises(RuntimeError):
        zero.eqTerm(x)
    with pytest.raises(RuntimeError):
        zero.eqTerm(f)
    with pytest.raises(RuntimeError):
        zero.eqTerm(p)
    zero.eqTerm(zero)
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
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
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
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
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
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
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
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


def test_imp_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.impTerm(b)
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    with pytest.raises(RuntimeError):
        x.impTerm(b)
    with pytest.raises(RuntimeError):
        x.impTerm(x)
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.impTerm(b)
    with pytest.raises(RuntimeError):
        f.impTerm(x)
    with pytest.raises(RuntimeError):
        f.impTerm(f)
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.impTerm(b)
    with pytest.raises(RuntimeError):
        p.impTerm(x)
    with pytest.raises(RuntimeError):
        p.impTerm(f)
    with pytest.raises(RuntimeError):
        p.impTerm(p)
    zero = tm.mkInteger(0)
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
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
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
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
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
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
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
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
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


def test_ite_term(tm):
    bvSort = tm.mkBitVectorSort(8)
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    funSort1 = tm.mkFunctionSort(bvSort, intSort)
    funSort2 = tm.mkFunctionSort(intSort, boolSort)

    b = tm.mkTrue()
    b.iteTerm(b, b)
    x = tm.mkVar(tm.mkBitVectorSort(8), "x")
    b.iteTerm(x, x)
    b.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        b.iteTerm(x, b)
    with pytest.raises(RuntimeError):
        x.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        x.iteTerm(x, b)
    f = tm.mkVar(funSort1, "f")
    with pytest.raises(RuntimeError):
        f.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        x.iteTerm(b, x)
    p = tm.mkVar(funSort2, "p")
    with pytest.raises(RuntimeError):
        p.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        p.iteTerm(x, b)
    zero = tm.mkInteger(0)
    with pytest.raises(RuntimeError):
        zero.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        zero.iteTerm(x, b)
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    with pytest.raises(RuntimeError):
        f_x.iteTerm(b, b)
    with pytest.raises(RuntimeError):
        f_x.iteTerm(b, x)
    sum = tm.mkTerm(Kind.ADD, f_x, f_x)
    with pytest.raises(RuntimeError):
        sum.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        sum.iteTerm(b, x)
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_0.iteTerm(b, b)
    p_0.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        p_0.iteTerm(x, b)
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_x.iteTerm(b, b)
    p_f_x.iteTerm(x, x)
    with pytest.raises(RuntimeError):
        p_f_x.iteTerm(x, b)


def test_term_assignment(tm):
    t1 = tm.mkInteger(1)
    t2 = t1
    t2 = tm.mkInteger(2)
    assert t1 == tm.mkInteger(1)


def test_substitute(tm):
    x = tm.mkConst(tm.getIntegerSort(), "x")
    one = tm.mkInteger(1)
    ttrue = tm.mkTrue()
    xpx = tm.mkTerm(Kind.ADD, x, x)
    onepone = tm.mkTerm(Kind.ADD, one, one)

    assert xpx.substitute(x, one) == onepone
    assert onepone.substitute(one, x) == xpx
    # incorrect due to type
    with pytest.raises(RuntimeError):
        xpx.substitute(one, ttrue)

    # simultaneous substitution
    y = tm.mkConst(tm.getIntegerSort(), "y")
    xpy = tm.mkTerm(Kind.ADD, x, y)
    xpone = tm.mkTerm(Kind.ADD, y, one)
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


def test_term_compare(tm):
    t1 = tm.mkInteger(1)
    t2 = tm.mkTerm(Kind.ADD, tm.mkInteger(2), tm.mkInteger(2))
    t3 = tm.mkTerm(Kind.ADD, tm.mkInteger(2), tm.mkInteger(2))
    assert t2 >= t3
    assert t2 <= t3
    assert (t1 > t2) != (t1 < t2)
    assert (t1 > t2 or t1 == t2) == (t1 >= t2)


def test_term_children(tm):
    # simple term 2+3
    two = tm.mkInteger(2)
    t1 = tm.mkTerm(Kind.ADD, two, tm.mkInteger(3))
    assert t1[0] == two
    assert t1.getNumChildren() == 2

    # apply term f(2)
    intSort = tm.getIntegerSort()
    fsort = tm.mkFunctionSort(intSort, intSort)
    f = tm.mkConst(fsort, "f")
    t2 = tm.mkTerm(Kind.APPLY_UF, f, two)
    # due to our higher-order view of terms, we treat f as a child of
    # Kind.APPLY_UF
    assert t2.getNumChildren() == 2
    assert t2[0] == f
    assert t2[1] == two


def test_get_const_array_base(tm):
    intsort = tm.getIntegerSort()
    arrsort = tm.mkArraySort(intsort, intsort)
    one = tm.mkInteger(1)
    constarr = tm.mkConstArray(arrsort, one)

    assert constarr.isConstArray()
    assert one == constarr.getConstArrayBase()

    with pytest.raises(RuntimeError):
        one.getConstArrayBase()

    a = tm.mkConst(arrsort, "a")
    with pytest.raises(RuntimeError):
        a.getConstArrayBase()


def test_get_uninterpreted_sort_value(tm, solver):
    solver.setOption("produce-models", "true")
    uSort = tm.mkUninterpretedSort("u")
    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    solver.assertFormula(tm.mkTerm(Kind.EQUAL, x, y))
    assert solver.checkSat().isSat()
    vx = solver.getValue(x)
    vy = solver.getValue(y)
    assert vx.isUninterpretedSortValue()
    assert vy.isUninterpretedSortValue()
    assert vx.getUninterpretedSortValue() == vy.getUninterpretedSortValue()


def test_is_rounding_mode_value(tm):
    assert not tm.mkInteger(15).isRoundingModeValue()
    assert tm.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).isRoundingModeValue()
    assert not tm.mkConst(
        tm.getRoundingModeSort()).isRoundingModeValue()


def test_get_rounding_mode_value(tm):
    with pytest.raises(RuntimeError):
        tm.mkInteger(15).getRoundingModeValue()
    assert tm.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).getRoundingModeValue(
        ) == RoundingMode.ROUND_NEAREST_TIES_TO_EVEN
    assert tm.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_POSITIVE).getRoundingModeValue(
        ) == RoundingMode.ROUND_TOWARD_POSITIVE
    assert tm.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_NEGATIVE).getRoundingModeValue(
        ) == RoundingMode.ROUND_TOWARD_NEGATIVE
    assert tm.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_ZERO).getRoundingModeValue(
        ) == RoundingMode.ROUND_TOWARD_ZERO
    assert tm.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).getRoundingModeValue(
        ) == RoundingMode.ROUND_NEAREST_TIES_TO_AWAY


def test_get_tuple(tm):
    t1 = tm.mkInteger(15)
    t2 = tm.mkReal(17, 25)
    t3 = tm.mkString("abc")

    tup = tm.mkTuple([t1, t2, t3])

    assert tup.isTupleValue()
    assert [t1, t2, t3] == tup.getTupleValue()


def test_get_set(tm, solver):
    s = tm.mkSetSort(tm.getIntegerSort())

    i1 = tm.mkInteger(5)
    i2 = tm.mkInteger(7)

    s1 = tm.mkEmptySet(s)
    s2 = tm.mkTerm(Kind.SET_SINGLETON, i1)
    s3 = tm.mkTerm(Kind.SET_SINGLETON, i1)
    s4 = tm.mkTerm(Kind.SET_SINGLETON, i2)
    s5 = tm.mkTerm(
            Kind.SET_UNION, s2, tm.mkTerm(Kind.SET_UNION, s3, s4))

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


def test_get_sequence(tm, solver):
    s = tm.mkSequenceSort(tm.getIntegerSort())

    i1 = tm.mkInteger(5)
    i2 = tm.mkInteger(7)

    s1 = tm.mkEmptySequence(s)
    s2 = tm.mkTerm(Kind.SEQ_UNIT, i1)
    s3 = tm.mkTerm(Kind.SEQ_UNIT, i1)
    s4 = tm.mkTerm(Kind.SEQ_UNIT, i2)
    s5 = tm.mkTerm(Kind.SEQ_CONCAT, s2,
                       tm.mkTerm(Kind.SEQ_CONCAT, s3, s4))

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


def test_get_floating_point(tm):
    bvval = tm.mkBitVector(16, "0000110000000011", 2)
    fp = tm.mkFloatingPoint(5, 11, bvval)

    assert fp.isFloatingPointValue()
    assert not fp.isFloatingPointPosZero()
    assert not fp.isFloatingPointNegZero()
    assert not fp.isFloatingPointPosInf()
    assert not fp.isFloatingPointNegInf()
    assert not fp.isFloatingPointNaN()
    assert (5, 11, bvval) == fp.getFloatingPointValue()

    assert tm.mkFloatingPointPosZero(5, 11).isFloatingPointPosZero()
    assert tm.mkFloatingPointNegZero(5, 11).isFloatingPointNegZero()
    assert tm.mkFloatingPointPosInf(5, 11).isFloatingPointPosInf()
    assert tm.mkFloatingPointNegInf(5, 11).isFloatingPointNegInf()
    assert tm.mkFloatingPointNaN(5, 11).isFloatingPointNaN()


def test_is_integer(tm):
    int1 = tm.mkInteger("-18446744073709551616")
    int2 = tm.mkInteger("-18446744073709551615")
    int3 = tm.mkInteger("-4294967296")
    int4 = tm.mkInteger("-4294967295")
    int5 = tm.mkInteger("-10")
    int6 = tm.mkInteger("0")
    int7 = tm.mkInteger("10")
    int8 = tm.mkInteger("4294967295")
    int9 = tm.mkInteger("4294967296")
    int10 = tm.mkInteger("18446744073709551615")
    int11 = tm.mkInteger("18446744073709551616")
    int12 = tm.mkInteger("-0")

    with pytest.raises(RuntimeError):
        tm.mkInteger("")
    with pytest.raises(RuntimeError):
        tm.mkInteger("-")
    with pytest.raises(RuntimeError):
        tm.mkInteger("-1-")
    with pytest.raises(RuntimeError):
        tm.mkInteger("0.0")
    with pytest.raises(RuntimeError):
        tm.mkInteger("-0.1")
    with pytest.raises(RuntimeError):
        tm.mkInteger("012")
    with pytest.raises(RuntimeError):
        tm.mkInteger("0000")
    with pytest.raises(RuntimeError):
        tm.mkInteger("-01")
    with pytest.raises(RuntimeError):
        tm.mkInteger("-00")

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


def test_get_string(tm):
    s1 = tm.mkString("abcde")
    assert s1.isStringValue()
    assert s1.getStringValue() == str("abcde")


def test_get_real(tm):
    real1 = tm.mkReal("0")
    real2 = tm.mkReal(".0")
    real3 = tm.mkReal("-17")
    real4 = tm.mkReal("-3/5")
    real5 = tm.mkReal("12.7")
    real6 = tm.mkReal("1/4294967297")
    real7 = tm.mkReal("4294967297")
    real8 = tm.mkReal("1/18446744073709551617")
    real9 = tm.mkReal("18446744073709551617")

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
    real_big = tm.mkReal(num, den)
    assert real_big.isRealValue()
    assert Fraction(num, den) == real_big.getRealValue()

    # Check that we're treating floats as decimal aproximations rather than
    # IEEE-754-specified values.
    real_decimal = tm.mkReal(0.3)
    assert real_decimal.isRealValue()
    assert Fraction("0.3") == real_decimal.getRealValue()
    assert Fraction(0.3) == Fraction(5404319552844595, 18014398509481984)
    assert Fraction(0.3) != real_decimal.getRealValue()
    
    with pytest.raises(RuntimeError):
        tm.mkReal("1/0")
    with pytest.raises(RuntimeError):
        tm.mkReal("2/0000")


def test_get_boolean(tm):
    b1 = tm.mkBoolean(True)
    b2 = tm.mkBoolean(False)

    assert b1.isBooleanValue()
    assert b2.isBooleanValue()
    assert b1.getBooleanValue()
    assert not b2.getBooleanValue()


def test_get_bit_vector(tm):
    b1 = tm.mkBitVector(8, 15)
    b2 = tm.mkBitVector(8, "00001111", 2)
    b3 = tm.mkBitVector(8, "15", 10)
    b4 = tm.mkBitVector(8, "0f", 16)
    b5 = tm.mkBitVector(9, "00001111", 2);
    b6 = tm.mkBitVector(9, "15", 10);
    b7 = tm.mkBitVector(9, "0f", 16);

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


def test_const_array(tm):
    intsort = tm.getIntegerSort()
    arrsort = tm.mkArraySort(intsort, intsort)
    a = tm.mkConst(arrsort, "a")
    one = tm.mkInteger(1)
    two = tm.mkBitVector(2, 2)
    iconst = tm.mkConst(intsort)
    constarr = tm.mkConstArray(arrsort, one)

    with pytest.raises(RuntimeError):
        tm.mkConstArray(arrsort, two)
    with pytest.raises(RuntimeError):
        tm.mkConstArray(arrsort, iconst)

    assert constarr.getKind() == Kind.CONST_ARRAY
    assert constarr.getConstArrayBase() == one
    with pytest.raises(RuntimeError):
        a.getConstArrayBase()

    arrsort = tm.mkArraySort(tm.getRealSort(), tm.getRealSort())
    zero_array = tm.mkConstArray(arrsort, tm.mkReal(0))
    stores = tm.mkTerm(Kind.STORE, zero_array, tm.mkReal(1),
                           tm.mkReal(2))
    stores = tm.mkTerm(Kind.STORE, stores, tm.mkReal(2),
                           tm.mkReal(3))
    stores = tm.mkTerm(Kind.STORE, stores, tm.mkReal(4),
                           tm.mkReal(5))


def test_const_sequence_elements(tm):
    realsort = tm.getRealSort()
    seqsort = tm.mkSequenceSort(realsort)
    s = tm.mkEmptySequence(seqsort)

    assert s.getKind() == Kind.CONST_SEQUENCE
    # empty sequence has zero elements
    cs = s.getSequenceValue()
    assert len(cs) == 0

    # A seq.unit app is not a constant sequence (regardless of whether it is
    # applied to a constant).
    su = tm.mkTerm(Kind.SEQ_UNIT, tm.mkReal(1))
    with pytest.raises(RuntimeError):
        su.getSequenceValue()

def test_get_cardinality_constraint(tm):
    su = tm.mkUninterpretedSort("u")
    t = tm.mkCardinalityConstraint(su, 3)
    assert t.isCardinalityConstraint()
    cc = t.getCardinalityConstraint()
    assert cc[0] == su
    assert cc[1] == 3
    x = tm.mkConst(tm.getIntegerSort(), "x")
    assert not x.isCardinalityConstraint()
    with pytest.raises(RuntimeError):
      x.getCardinalityConstraint()

def test_get_real_algebraic_number(tm, solver):
    solver.setOption("produce-models", "true")
    solver.setLogic("QF_NRA")
    realsort = tm.getRealSort()
    x = tm.mkConst(realsort, "x")
    x2 = tm.mkTerm(Kind.MULT, x, x)
    two = tm.mkReal(2, 1)
    eq = tm.mkTerm(Kind.EQUAL, x2, two)
    solver.assertFormula(eq)
    # Note that check-sat should only return "sat" if libpoly is enabled.
    # Otherwise, we do not test the following functionality.
    if solver.checkSat().isSat():
        # We find a model for (x*x = 2), where x should be a real algebraic number.
        # We assert that its defining polynomial is non-null and its lower and
        # upper bounds are real.
        vx = solver.getValue(x)
        assert vx.isRealAlgebraicNumber()
        y = tm.mkVar(realsort, "y")
        poly = vx.getRealAlgebraicNumberDefiningPolynomial(y)
        assert not poly.isNull()
        lb = vx.getRealAlgebraicNumberLowerBound()
        assert lb.isRealValue()
        ub = vx.getRealAlgebraicNumberUpperBound()
        assert ub.isRealValue()
        # cannot call with non-variable
        yc = tm.mkConst(realsort, "y")
        with pytest.raises(RuntimeError):
            vx.getRealAlgebraicNumberDefiningPolynomial(yc)

def test_get_skolem(tm, solver):
    # ordinary variables are not skolems
    x = tm.mkConst(tm.getIntegerSort(), "x")
    assert not x.isSkolem()
    with pytest.raises(RuntimeError):
        x.getSkolemId()
    with pytest.raises(RuntimeError):
        x.getSkolemIndices()
    

def test_term_scoped_to_string(tm):
    intsort = tm.getIntegerSort()
    x = tm.mkConst(intsort, "x")
    assert str(x) == "x"
    tm2 = cvc5.Solver(tm)
    assert str(x) == "x"
