###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Amalee Wilson, Ying Sheng
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
import sys

from cvc5 import Kind, SortKind, RoundingMode, TermManager, Solver

@pytest.fixture
def tm():
    return TermManager()
@pytest.fixture
def solver(tm):
    return Solver(tm)

def test_get_boolean_sort(tm):
    tm.getBooleanSort()


def test_get_integer_sort(tm):
    tm.getIntegerSort()


def test_get_real_sort(tm):
    tm.getRealSort()


def test_get_reg_exp_sort(tm):
    tm.getRegExpSort()


def test_get_string_sort(tm):
    tm.getStringSort()


def test_get_rounding_mode_sort(tm):
    tm.getRoundingModeSort()


def test_mk_array_sort(tm):
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    realSort = tm.getRealSort()
    bvSort = tm.mkBitVectorSort(32)
    tm.mkArraySort(boolSort, boolSort)
    tm.mkArraySort(intSort, intSort)
    tm.mkArraySort(realSort, realSort)
    tm.mkArraySort(bvSort, bvSort)
    tm.mkArraySort(boolSort, intSort)
    tm.mkArraySort(realSort, bvSort)

    fpSort = tm.mkFloatingPointSort(3, 5)
    tm.mkArraySort(fpSort, fpSort)
    tm.mkArraySort(bvSort, fpSort)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkArraySort(ttm.getBooleanSort(), ttm.getIntegerSort())

def test_mk_bit_vector_sort(tm):
    tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        tm.mkBitVectorSort(0)


def test_mk_finite_field_sort(tm):
    tm.mkFiniteFieldSort("31")
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("6")

    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("b")

    tm.mkFiniteFieldSort(17)
    tm.mkFiniteFieldSort(0x65)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort(12)

    tm.mkFiniteFieldSort("b", 16)
    with pytest.raises(ValueError):
        tm.mkFiniteFieldSort(0xb, 16)

    tm.mkFiniteFieldSort("1100101",2)
    tm.mkFiniteFieldSort("10202", 3)
    tm.mkFiniteFieldSort("401",   5)
    tm.mkFiniteFieldSort("791a", 11)
    tm.mkFiniteFieldSort("970f", 16)
    tm.mkFiniteFieldSort("8CC5", 16)

    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("1100100",2)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("10201", 3)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("400",   5)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("7919", 11)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("970e", 16)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("8CC4", 16)


def test_mk_floating_point_sort(tm):
    tm.mkFloatingPointSort(4, 8)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPointSort(0, 8)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPointSort(4, 0)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPointSort(1, 8)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPointSort(4, 1)


def test_mk_datatype_sort(tm):
    dtypeSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", tm.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    tm.mkDatatypeSort(dtypeSpec)

    with pytest.raises(RuntimeError):
        tm.mkDatatypeSort(dtypeSpec)
    slv = Solver(tm)
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSort(dtypeSpec)

    throwsDtypeSpec = tm.mkDatatypeDecl("list")
    with pytest.raises(RuntimeError):
        tm.mkDatatypeSort(throwsDtypeSpec)

    ttm = TermManager()
    dtypeSpec = ttm.mkDatatypeDecl("list")
    cons = ttm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", ttm.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = ttm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkDatatypeSort(dtypeSpec)


def test_mk_datatype_sorts(tm):
    dtypeSpec1 = tm.mkDatatypeDecl("list1")
    cons1 = tm.mkDatatypeConstructorDecl("cons1")
    cons1.addSelector("head1", tm.getIntegerSort())
    dtypeSpec1.addConstructor(cons1)
    nil1 = tm.mkDatatypeConstructorDecl("nil1")
    dtypeSpec1.addConstructor(nil1)

    dtypeSpec2 = tm.mkDatatypeDecl("list2")
    cons2 = tm.mkDatatypeConstructorDecl("cons2")
    cons2.addSelector("head2", tm.getIntegerSort())
    dtypeSpec2.addConstructor(cons2)
    nil2 = tm.mkDatatypeConstructorDecl("nil2")
    dtypeSpec2.addConstructor(nil2)

    decls = [dtypeSpec1, dtypeSpec2]
    tm.mkDatatypeSorts(decls)

    with pytest.raises(RuntimeError):
        tm.mkDatatypeSorts(decls)

    throwsDtypeSpec = tm.mkDatatypeDecl("list")
    throwsDecls = [throwsDtypeSpec]
    with pytest.raises(RuntimeError):
        tm.mkDatatypeSorts(throwsDecls)

    # with unresolved sorts
    unresList = tm.mkUnresolvedDatatypeSort("ulist")
    ulist = tm.mkDatatypeDecl("ulist")
    ucons = tm.mkDatatypeConstructorDecl("ucons")
    ucons.addSelector("car", unresList)
    ucons.addSelector("cdr", unresList)
    ulist.addConstructor(ucons)
    unil = tm.mkDatatypeConstructorDecl("unil")
    ulist.addConstructor(unil)
    udecls = [ulist]

    tm.mkDatatypeSorts(udecls)
    with pytest.raises(RuntimeError):
        tm.mkDatatypeSorts(udecls)

    # mutually recursive with unresolved parameterized sorts
    p0 = tm.mkParamSort("p0")
    p1 = tm.mkParamSort("p1")
    u0 = tm.mkUnresolvedDatatypeSort("dt0", 1)
    u1 = tm.mkUnresolvedDatatypeSort("dt1", 1)
    dtdecl0 = tm.mkDatatypeDecl("dt0", [p0])
    dtdecl1 = tm.mkDatatypeDecl("dt1", [p1])
    ctordecl0 = tm.mkDatatypeConstructorDecl("c0")
    ctordecl0.addSelector("s0", u1.instantiate([p0]))
    ctordecl1 = tm.mkDatatypeConstructorDecl("c1")
    ctordecl1.addSelector("s1", u0.instantiate([p1]))
    dtdecl0.addConstructor(ctordecl0)
    dtdecl1.addConstructor(ctordecl1)
    dtdecl1.addConstructor(tm.mkDatatypeConstructorDecl("nil"))
    dt_sorts = tm.mkDatatypeSorts([dtdecl0, dtdecl1])
    isort1 = dt_sorts[1].instantiate([tm.getBooleanSort()])
    t1 = tm.mkConst(isort1, "t")
    t0 = tm.mkTerm(
        Kind.APPLY_SELECTOR,
        t1.getSort().getDatatype().getSelector("s1").getTerm(),
        t1)
    assert dt_sorts[0].instantiate([tm.getBooleanSort()]) == t0.getSort()

    ttm = TermManager()
    dtypeSpec1 = ttm.mkDatatypeDecl("list1")
    cons1 = ttm.mkDatatypeConstructorDecl("cons1")
    cons1.addSelector("head1", ttm.getIntegerSort())
    dtypeSpec1.addConstructor(cons1)
    dtypeSpec1.addConstructor(ttm.mkDatatypeConstructorDecl("nil1"))
    dtypeSpec2 = ttm.mkDatatypeDecl("list2")
    cons2 = ttm.mkDatatypeConstructorDecl("cons2")
    cons2.addSelector("head2", ttm.getIntegerSort())
    dtypeSpec2.addConstructor(cons2)
    dtypeSpec2.addConstructor(ttm.mkDatatypeConstructorDecl("nil2"))
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkDatatypeSorts([dtypeSpec1, dtypeSpec2])


def test_mk_function_sort(tm):
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),\
            tm.getIntegerSort())

    # function arguments are allowed
    tm.mkFunctionSort(funSort, tm.getIntegerSort())

    # non-first-class arguments are not allowed
    reSort = tm.getRegExpSort()
    with pytest.raises(RuntimeError):
        tm.mkFunctionSort(reSort, tm.getIntegerSort())
    with pytest.raises(RuntimeError):
        tm.mkFunctionSort(tm.getIntegerSort(), funSort)

    tm.mkFunctionSort([tm.mkUninterpretedSort("u"),\
            tm.getIntegerSort()],\
            tm.getIntegerSort())
    funSort2 = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),\
            tm.getIntegerSort())

    # function arguments are allowed
    tm.mkFunctionSort([funSort2, tm.mkUninterpretedSort("u")],\
            tm.getIntegerSort())

    with pytest.raises(RuntimeError):
        tm.mkFunctionSort([tm.getIntegerSort(),\
                tm.mkUninterpretedSort("u")],\
                funSort2)

    sorts1 = [tm.getBooleanSort(),\
            tm.getIntegerSort(),\
            tm.getIntegerSort()]
    sorts2 = [tm.getBooleanSort(), tm.getIntegerSort()]
    tm.mkFunctionSort(sorts2, tm.getIntegerSort())
    tm.mkFunctionSort(sorts1, tm.getIntegerSort())
    tm.mkFunctionSort(sorts2, tm.getIntegerSort())

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkFunctionSort(sorts2, ttm.getIntegerSort())
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkFunctionSort(
            [ttm.getBooleanSort(), ttm.getIntegerSort()], tm.getIntegerSort())


def test_mk_param_sort(tm):
    tm.mkParamSort("T")
    tm.mkParamSort("")

def test_mk_skolem(tm):
    integer = tm.getIntegerSort()
    arraySort = tm.mkArraySort(integer, integer)
    a = tm.mkConst(arraySort, "a")
    b = tm.mkConst(arraySort, "b")

    sk = tm.mkSkolem(cvc5.SkolemId.ARRAY_DEQ_DIFF, a, b)
    sk2 = tm.mkSkolem(cvc5.SkolemId.ARRAY_DEQ_DIFF, b, a)

    assert sk.isSkolem()
    assert sk2.isSkolem()
    assert sk.getSkolemId() == cvc5.SkolemId.ARRAY_DEQ_DIFF
    assert sk2.getSkolemId() == cvc5.SkolemId.ARRAY_DEQ_DIFF
    assert sk.getSkolemIndices() == [a, b]
    # ARRAY_DEQ_DIFF is commutative, so the order of the indices is sorted.
    assert sk2.getSkolemIndices() == [a, b]

def test_skolem_num_indices(tm):
    num = tm.getNumIndicesForSkolemId(cvc5.SkolemId.ARRAY_DEQ_DIFF)
    assert num == 2

def test_mk_predicate_sort(tm):
    tm.mkPredicateSort(tm.getIntegerSort())
    with pytest.raises(RuntimeError):
        tm.mkPredicateSort()

    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),\
            tm.getIntegerSort())
    # functions as arguments are allowed
    tm.mkPredicateSort(tm.getIntegerSort(), funSort)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkPredicateSort(tm.getIntegerSort())


def test_mk_record_sort(tm):
    fields = [("b", tm.getBooleanSort()),\
              ("bv", tm.mkBitVectorSort(8)),\
              ("i", tm.getIntegerSort())]
    tm.mkRecordSort(*fields)
    tm.mkRecordSort()
    recSort = tm.mkRecordSort(*fields)
    recSort.getDatatype()

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkRecordSort(
                ("b", ttm.getBooleanSort()), \
                ("bv", tm.mkBitVectorSort(8)), \
                ("i", ttm.getIntegerSort())
            )


def test_mk_set_sort(tm):
    tm.mkSetSort(tm.getBooleanSort())
    tm.mkSetSort(tm.getIntegerSort())
    tm.mkSetSort(tm.mkBitVectorSort(4))

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkSetSort(ttm.getBooleanSort())


def test_mk_bag_sort(tm):
    tm.mkBagSort(tm.getBooleanSort())
    tm.mkBagSort(tm.getIntegerSort())
    tm.mkBagSort(tm.mkBitVectorSort(4))

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkBagSort(ttm.getBooleanSort())


def test_mk_sequence_sort(tm):
    tm.mkSequenceSort(tm.getBooleanSort())
    tm.mkSequenceSort(\
            tm.mkSequenceSort(tm.getIntegerSort()))

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkSequenceSort(ttm.getBooleanSort())


def test_mk_abstract_sort(tm):
    tm.mkAbstractSort(SortKind.ARRAY_SORT)
    tm.mkAbstractSort(SortKind.BITVECTOR_SORT)
    tm.mkAbstractSort(SortKind.TUPLE_SORT)
    tm.mkAbstractSort(SortKind.SET_SORT)
    with pytest.raises(RuntimeError):
        tm.mkAbstractSort(SortKind.BOOLEAN_SORT)


def test_mk_uninterpreted_sort(tm):
    tm.mkUninterpretedSort("u")
    tm.mkUninterpretedSort("")


def test_mk_unresolved_sort(tm):
    tm.mkUnresolvedDatatypeSort("u")
    tm.mkUnresolvedDatatypeSort("u", 1)
    tm.mkUnresolvedDatatypeSort("")
    tm.mkUnresolvedDatatypeSort("", 1)


def test_mk_sort_constructor_sort(tm):
    tm.mkUninterpretedSortConstructorSort(2, "s")
    tm.mkUninterpretedSortConstructorSort(2)
    with pytest.raises(RuntimeError):
        tm.mkUninterpretedSortConstructorSort(0)


def test_mk_tuple_sort(tm):
    tm.mkTupleSort(tm.getIntegerSort())
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),\
                                    tm.getIntegerSort())
    tm.mkTupleSort(tm.getIntegerSort(), funSort)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkTupleSort(ttm.getBooleanSort())


def test_mk_nullable_sort(tm, solver):
    nullable_sort = tm.mkNullableSort(tm.getBooleanSort())
    nullable_null = tm.mkNullableNull(nullable_sort)
    value = tm.mkNullableIsNull(nullable_null)
    value = solver.simplify(value)
    assert value.getBooleanValue()

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkNullableSort(ttm.getIntegerSort())


def test_mk_bit_vector(tm):
    tm.mkBitVector(8, 2)
    tm.mkBitVector(32, 2)
    tm.mkBitVector(64, 2**33)

    tm.mkBitVector(4, "1010", 2)
    tm.mkBitVector(8, "0101", 2)
    tm.mkBitVector(8, "-1111111", 2)
    tm.mkBitVector(8, "00000101", 2)
    tm.mkBitVector(8, "-127", 10)
    tm.mkBitVector(8, "255", 10)
    tm.mkBitVector(10, "1010", 10)
    tm.mkBitVector(11, "1234", 10)
    tm.mkBitVector(8, "-7f", 16)
    tm.mkBitVector(8, "a0", 16)
    tm.mkBitVector(16, "1010", 16)
    tm.mkBitVector(16, "a09f", 16)

    with pytest.raises(RuntimeError):
        tm.mkBitVector(0, 2)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(0, "-127", 10)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(0, "a0", 16)

    with pytest.raises(RuntimeError):
        tm.mkBitVector(2, "", 2)

    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "101", 5)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "127", 11)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "a0", 21)

    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "101010101", 2)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "-11111111", 2)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "-256", 10)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "257", 10)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "-a0", 16)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "fffff", 16)

    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "10201010", 2)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "-25x", 10)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "2x7", 10)
    with pytest.raises(RuntimeError):
        tm.mkBitVector(8, "fzff", 16)

    assert tm.mkBitVector(8, "0101",
                              2) == tm.mkBitVector(8, "00000101", 2)
    assert tm.mkBitVector(4, "1010", 2) == tm.mkBitVector(4, "10", 10)
    assert tm.mkBitVector(4, "1010", 2) == tm.mkBitVector(4, "a", 16)
    assert str(tm.mkBitVector(8, "01010101", 2)) == "#b01010101"
    assert str(tm.mkBitVector(8, "F", 16)) == "#b00001111"
    assert tm.mkBitVector(8, "-1", 10) ==\
            tm.mkBitVector(8, "FF", 16)


def test_mk_finite_field_elem(tm):
    bv = tm.mkBitVectorSort(4)
    with pytest.raises(RuntimeError):
      tm.mkFiniteFieldElem("-1", bv)
    with pytest.raises(ValueError):
        tm.mkFiniteFieldElem(tm, bv)

    f = tm.mkFiniteFieldSort("7");

    tm.mkFiniteFieldElem("0", f)
    tm.mkFiniteFieldElem("1", f)
    tm.mkFiniteFieldElem("6", f)
    tm.mkFiniteFieldElem("8", f)
    tm.mkFiniteFieldElem("-1", f)

    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldElem("b", f)

    tm.mkFiniteFieldElem(10, f)

    tm.mkFiniteFieldSort("b", 16)
    with pytest.raises(RuntimeError):
        tm.mkFiniteFieldSort("a", 16)

    tm.mkFiniteFieldElem("18", f, 16)
    with pytest.raises(ValueError):
        tm.mkFiniteFieldElem(0x18, f, 16)

    assert tm.mkFiniteFieldElem(10, f) == tm.mkFiniteFieldElem("10", f)

    assert tm.mkFiniteFieldElem("-1", f) == tm.mkFiniteFieldElem("6", f)
    assert tm.mkFiniteFieldElem("1", f) == tm.mkFiniteFieldElem("8", f)

    tm.mkFiniteFieldElem("0", f, 2)
    tm.mkFiniteFieldElem("101", f, 3)
    tm.mkFiniteFieldElem("-10", f, 7)
    tm.mkFiniteFieldElem("abcde", f, 16)

    assert tm.mkFiniteFieldElem("0", f, 2) \
            == tm.mkFiniteFieldElem("0", f, 3)
    assert tm.mkFiniteFieldElem("11", f, 2) \
            == tm.mkFiniteFieldElem("10", f, 3)
    assert tm.mkFiniteFieldElem("1010", f, 2) \
            == tm.mkFiniteFieldElem("A", f, 16)
    assert tm.mkFiniteFieldElem("-22", f, 3) \
            == tm.mkFiniteFieldElem("10", f, 6)


def test_mk_var(tm):
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    funSort = tm.mkFunctionSort(intSort, boolSort)
    tm.mkVar(boolSort)
    tm.mkVar(funSort)
    tm.mkVar(boolSort, "b")
    tm.mkVar(funSort, "")


def test_mk_boolean(tm):
    tm.mkBoolean(True)
    tm.mkBoolean(False)


def test_mk_rounding_mode(tm):
    assert str(tm.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN)) == "roundNearestTiesToEven"
    assert str(tm.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_POSITIVE)) == "roundTowardPositive"
    assert str(tm.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_NEGATIVE)) == "roundTowardNegative"
    assert str(tm.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_ZERO)) == "roundTowardZero"
    assert str(tm.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_AWAY)) == "roundNearestTiesToAway"


def test_mk_floating_point(tm):
    t1 = tm.mkBitVector(8)
    t2 = tm.mkBitVector(4)
    t3 = tm.mkInteger(2)
    tm.mkFloatingPoint(3, 5, t1)

    with pytest.raises(RuntimeError):
        tm.mkFloatingPoint(0, 5, t1)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPoint(3, 0, t1)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPoint(3, 5, t2)
    with pytest.raises(RuntimeError):
        tm.mkFloatingPoint(3, 5, t2)

    sign = tm.mkBitVector(1)
    exp = tm.mkBitVector(5)
    sig = tm.mkBitVector(10)
    bv = tm.mkBitVector(16)
    a = tm.mkFloatingPoint(
            sign, exp, sig)
    assert tm.mkFloatingPoint(
            sign, exp, sig) == tm.mkFloatingPoint(5, 11, bv)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkFloatingPoint(3, 5, t1)
    #with pytest.raises(RuntimeError):
    ttm.mkFloatingPoint(
            tm.mkBitVector(1), ttm.mkBitVector(5), ttm.mkBitVector(10))
    #with pytest.raises(RuntimeError):
    ttm.mkFloatingPoint(
            ttm.mkBitVector(1), tm.mkBitVector(5), ttm.mkBitVector(10))
    #with pytest.raises(RuntimeError):
    ttm.mkFloatingPoint(
            ttm.mkBitVector(1), ttm.mkBitVector(5), tm.mkBitVector(10))


def test_mk_cardinality_constraint(tm):
    su = tm.mkUninterpretedSort("u")
    si = tm.getIntegerSort()
    tm.mkCardinalityConstraint(su, 3)
    with pytest.raises(RuntimeError):
        tm.mkEmptySet(tm.mkCardinalityConstraint(si, 3))
    with pytest.raises(RuntimeError):
        tm.mkEmptySet(tm.mkCardinalityConstraint(su, 0))

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkCardinalityConstraint(su, 3)


def test_mk_empty_set(tm):
    s = tm.mkSetSort(tm.getBooleanSort())
    tm.mkEmptySet(s)
    with pytest.raises(RuntimeError):
        tm.mkEmptySet(tm.getBooleanSort())

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkEmptySet(s)


def test_mk_empty_bag(tm):
    s = tm.mkBagSort(tm.getBooleanSort())
    tm.mkEmptyBag(s)
    with pytest.raises(RuntimeError):
        tm.mkEmptyBag(tm.getBooleanSort())

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkEmptyBag(s)


def test_mk_empty_sequence(tm):
    s = tm.mkSequenceSort(tm.getBooleanSort())
    tm.mkEmptySequence(s)
    tm.mkEmptySequence(tm.getBooleanSort())

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkEmptySequence(s)


def test_mk_false(tm):
    tm.mkFalse()
    tm.mkFalse()


def test_mk_floating_point_nan(tm):
    tm.mkFloatingPointNaN(3, 5)


def test_mk_floating_point_neg_zero(tm):
    tm.mkFloatingPointNegZero(3, 5)


def test_mk_floating_point_neg_inf(tm):
    tm.mkFloatingPointNegInf(3, 5)


def test_mk_floating_point_pos_inf(tm):
    tm.mkFloatingPointPosInf(3, 5)


def test_mk_floating_point_pos_zero(tm):
    tm.mkFloatingPointPosZero(3, 5)


def test_mk_op(tm):
    with pytest.raises(ValueError):
        tm.mkOp(Kind.BITVECTOR_EXTRACT, Kind.EQUAL)

    tm.mkOp(Kind.DIVISIBLE, "2147483648")
    with pytest.raises(RuntimeError):
        tm.mkOp(Kind.BITVECTOR_EXTRACT, "asdf")

    tm.mkOp(Kind.DIVISIBLE, 1)
    tm.mkOp(Kind.BITVECTOR_ROTATE_LEFT, 1)
    tm.mkOp(Kind.BITVECTOR_ROTATE_RIGHT, 1)
    with pytest.raises(RuntimeError):
        tm.mkOp(Kind.BITVECTOR_EXTRACT, 1)

    tm.mkOp(Kind.BITVECTOR_EXTRACT, 1, 1)
    with pytest.raises(RuntimeError):
        tm.mkOp(Kind.DIVISIBLE, 1, 2)

    args = [1, 2, 2]
    tm.mkOp(Kind.TUPLE_PROJECT, *args)


def test_mk_pi(tm):
    tm.mkPi()


def test_mk_integer(tm):
    tm.mkInteger("123")
    with pytest.raises(RuntimeError):
        tm.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        tm.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        tm.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        tm.mkInteger(".2")
    with pytest.raises(RuntimeError):
        tm.mkInteger("2.")
    with pytest.raises(RuntimeError):
        tm.mkInteger("")
    with pytest.raises(RuntimeError):
        tm.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        tm.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        tm.mkInteger(".")
    with pytest.raises(RuntimeError):
        tm.mkInteger("/")
    with pytest.raises(RuntimeError):
        tm.mkInteger("2/")
    with pytest.raises(RuntimeError):
        tm.mkInteger("/2")

    tm.mkReal("123")
    with pytest.raises(RuntimeError):
        tm.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        tm.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        tm.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        tm.mkInteger(".2")
    with pytest.raises(RuntimeError):
        tm.mkInteger("2.")
    with pytest.raises(RuntimeError):
        tm.mkInteger("")
    with pytest.raises(RuntimeError):
        tm.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        tm.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        tm.mkInteger(".")
    with pytest.raises(RuntimeError):
        tm.mkInteger("/")
    with pytest.raises(RuntimeError):
        tm.mkInteger("2/")
    with pytest.raises(RuntimeError):
        tm.mkInteger("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    tm.mkInteger(val1)
    tm.mkInteger(val2)
    tm.mkInteger(val3)
    tm.mkInteger(val4)
    tm.mkInteger(val4)


def test_mk_real(tm):
    tm.mkReal("123")
    tm.mkReal("1.23")
    tm.mkReal("1/23")
    tm.mkReal("12/3")
    tm.mkReal(".2")
    tm.mkReal("2.")
    with pytest.raises(RuntimeError):
        tm.mkReal("")
    with pytest.raises(RuntimeError):
        tm.mkReal("asdf")
    with pytest.raises(RuntimeError):
        tm.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        tm.mkReal(".")
    with pytest.raises(RuntimeError):
        tm.mkReal("/")
    with pytest.raises(RuntimeError):
        tm.mkReal("2/")
    with pytest.raises(RuntimeError):
        tm.mkReal("/2")

    tm.mkReal("123")
    tm.mkReal("1.23")
    tm.mkReal("1/23")
    tm.mkReal("12/3")
    tm.mkReal(".2")
    tm.mkReal("2.")
    with pytest.raises(RuntimeError):
        tm.mkReal("")
    with pytest.raises(RuntimeError):
        tm.mkReal("asdf")
    with pytest.raises(RuntimeError):
        tm.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        tm.mkReal(".")
    with pytest.raises(RuntimeError):
        tm.mkReal("/")
    with pytest.raises(RuntimeError):
        tm.mkReal("2/")
    with pytest.raises(RuntimeError):
        tm.mkReal("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    tm.mkReal(val1)
    tm.mkReal(val2)
    tm.mkReal(val3)
    tm.mkReal(val4)
    tm.mkReal(val4)
    tm.mkReal(val1, val1)
    tm.mkReal(val2, val2)
    tm.mkReal(val3, val3)
    tm.mkReal(val4, val4)

    tm.mkReal("1", "2")
    tm.mkReal("-1", "2")
    tm.mkReal(-1, "2")
    tm.mkReal("-1", 2)
    with pytest.raises(TypeError):
        tm.mkReal(1, 2, 3)
    with pytest.raises(RuntimeError):
        tm.mkReal("1.0", 2)
    with pytest.raises(RuntimeError):
        tm.mkReal(1, "asdf")


def test_mk_regexp_none(tm):
    strSort = tm.getStringSort()
    s = tm.mkConst(strSort, "s")
    tm.mkTerm(Kind.STRING_IN_REGEXP, s, tm.mkRegexpNone())


def test_mk_regexp_all(tm):
    strSort = tm.getStringSort()
    s = tm.mkConst(strSort, "s")
    tm.mkTerm(Kind.STRING_IN_REGEXP, s, tm.mkRegexpAll())


def test_mk_regexp_allchar(tm):
    strSort = tm.getStringSort()
    s = tm.mkConst(strSort, "s")
    tm.mkTerm(Kind.STRING_IN_REGEXP, s, tm.mkRegexpAllchar())


def test_mk_sep_emp(tm):
    tm.mkSepEmp()


def test_mk_sep_nil(tm):
    tm.mkSepNil(tm.getBooleanSort())
    tm.mkSepNil(tm.getIntegerSort())

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkSepNil(tm.getBooleanSort())


def test_mk_string(tm):
    tm.mkString("")
    tm.mkString("asdfasdf")
    str(tm.mkString("asdf\\nasdf")) == "\"asdf\\u{5c}nasdf\""
    str(tm.mkString("asdf\\u{005c}nasdf", True)) ==\
            "\"asdf\\u{5c}nasdf\""
    s = ""
    assert tm.mkString(s).getStringValue() == s


def test_mk_term(tm):
    bv32 = tm.mkBitVectorSort(32)
    a = tm.mkConst(bv32, "a")
    b = tm.mkConst(bv32, "b")

    # mkTerm(Kind kind) const
    tm.mkPi()
    tm.mkTerm(Kind.PI)
    tm.mkTerm(tm.mkOp(Kind.PI))
    tm.mkTerm(Kind.REGEXP_NONE)
    tm.mkTerm(tm.mkOp(Kind.REGEXP_NONE))
    tm.mkTerm(Kind.REGEXP_ALLCHAR)
    tm.mkTerm(tm.mkOp(Kind.REGEXP_ALLCHAR))
    tm.mkTerm(Kind.SEP_EMP)
    tm.mkTerm(tm.mkOp(Kind.SEP_EMP))
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.CONST_BITVECTOR)

    # mkTerm(Kind kind, Term child) const
    tm.mkTerm(Kind.NOT, tm.mkTrue())
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.NOT, a)

    # mkTerm(Kind kind, Term child1, Term child2) const
    tm.mkTerm(Kind.EQUAL, a, b)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.EQUAL, a, tm.mkTrue())

    # mkTerm(Kind kind, Term child1, Term child2, Term child3) const
    tm.mkTerm(Kind.ITE, tm.mkTrue(), tm.mkTrue(), tm.mkTrue())
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.ITE, tm.mkTrue(), tm.mkTrue(), b)

    tm.mkTerm(Kind.EQUAL, a, b)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.EQUAL, a, tm.mkTrue())
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.DISTINCT)

    # Test cases that are nary via the API but have arity = 2 internally
    s_bool = tm.getBooleanSort()
    t_bool = tm.mkConst(s_bool, "t_bool")
    tm.mkTerm(Kind.IMPLIES, t_bool, t_bool, t_bool)
    tm.mkTerm(Kind.XOR, t_bool, t_bool, t_bool)
    tm.mkTerm(tm.mkOp(Kind.XOR), t_bool, t_bool, t_bool)
    t_int = tm.mkConst(tm.getIntegerSort(), "t_int")
    tm.mkTerm(Kind.DIVISION, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.DIVISION), t_int, t_int, t_int)
    tm.mkTerm(Kind.INTS_DIVISION, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.INTS_DIVISION), t_int, t_int, t_int)
    tm.mkTerm(Kind.SUB, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.SUB), t_int, t_int, t_int)
    tm.mkTerm(Kind.EQUAL, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.EQUAL), t_int, t_int, t_int)
    tm.mkTerm(Kind.LT, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.LT), t_int, t_int, t_int)
    tm.mkTerm(Kind.GT, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.GT), t_int, t_int, t_int)
    tm.mkTerm(Kind.LEQ, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.LEQ), t_int, t_int, t_int)
    tm.mkTerm(Kind.GEQ, t_int, t_int, t_int)
    tm.mkTerm(tm.mkOp(Kind.GEQ), t_int, t_int, t_int)
    t_reg = tm.mkConst(tm.getRegExpSort(), "t_reg")
    tm.mkTerm(Kind.REGEXP_DIFF, t_reg, t_reg, t_reg)
    tm.mkTerm(tm.mkOp(Kind.REGEXP_DIFF), t_reg, t_reg, t_reg)
    t_fun = tm.mkConst(tm.mkFunctionSort(
        [s_bool, s_bool, s_bool], s_bool))
    tm.mkTerm(Kind.HO_APPLY, t_fun, t_bool, t_bool, t_bool)
    tm.mkTerm(tm.mkOp(Kind.HO_APPLY), t_fun, t_bool, t_bool, t_bool)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    tm.mkTerm(Kind.ITE, tm.mkTrue(), ttm.mkTrue(), ttm.mkTrue())
    tm.mkTerm(Kind.ITE, ttm.mkTrue(), tm.mkTrue(), ttm.mkTrue())
    tm.mkTerm(Kind.ITE, ttm.mkTrue(), ttm.mkTrue(), tm.mkTrue())


def test_mk_term_from_op(tm):
    bv32 = tm.mkBitVectorSort(32)
    a = tm.mkConst(bv32, "a")
    b = tm.mkConst(bv32, "b")

    # simple operator terms
    opterm1 = tm.mkOp(Kind.BITVECTOR_EXTRACT, 2, 1)
    opterm2 = tm.mkOp(Kind.DIVISIBLE, 1)

    # list datatype
    sort = tm.mkParamSort("T")
    listDecl = tm.mkDatatypeDecl("paramlist", [sort])
    cons = tm.mkDatatypeConstructorDecl("cons")
    nil = tm.mkDatatypeConstructorDecl("nil")
    cons.addSelector("head", sort)
    cons.addSelectorSelf("tail")
    listDecl.addConstructor(cons)
    listDecl.addConstructor(nil)
    listSort = tm.mkDatatypeSort(listDecl)
    intListSort =\
        listSort.instantiate([tm.getIntegerSort()])
    c = tm.mkConst(intListSort, "c")
    lis = listSort.getDatatype()

    # list datatype constructor and selector operator terms
    consTerm = lis.getConstructor("cons").getTerm()
    nilTerm = lis.getConstructor("nil").getTerm()
    headTerm = lis["cons"].getSelector("head").getTerm()
    tailTerm = lis["cons"]["tail"].getTerm()

    # mkTerm(Op op, Term term) const
    tm.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm)
    tm.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.APPLY_SELECTOR, nilTerm)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.APPLY_SELECTOR, consTerm)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm)
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm1)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.APPLY_SELECTOR, headTerm)
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm1)

    # mkTerm(Op op, Term child) const
    tm.mkTerm(opterm1, a)
    tm.mkTerm(opterm2, tm.mkInteger(1))
    tm.mkTerm(Kind.APPLY_SELECTOR, headTerm, c)
    tm.mkTerm(Kind.APPLY_SELECTOR, tailTerm, c)
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm2, a)
    with pytest.raises(RuntimeError):
        tm.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm, tm.mkInteger(0))

    # mkTerm(Op op, Term child1, Term child2) const
    tm.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm, tm.mkInteger(0),
                  tm.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm))
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm2, tm.mkInteger(1), tm.mkInteger(2))
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm1, a, b)

    # mkTerm(Op op, Term child1, Term child2, Term child3) const
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm1, a, b, a)

    tm.mkTerm(opterm2, tm.mkInteger(5))
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm2, tm.mkInteger(1), tm.mkInteger(2))
    with pytest.raises(RuntimeError):
        tm.mkTerm(opterm2)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkTerm(opterm2, ttm.mkInteger(1))
    ttm.mkTerm(ttm.mkOp(Kind.DIVISIBLE, 1), tm.mkInteger(1))


def test_mk_true(tm):
    tm.mkTrue()
    tm.mkTrue()


def test_mk_tuple(tm):
    tm.mkTuple([tm.mkBitVector(3, "101", 2)])
    tm.mkTuple([tm.mkInteger("5")])
    tm.mkTuple([tm.mkReal("5.3")])

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkTuple([tm.mkBitVector(3, "101", 2)])


def test_mk_nullable_some(tm):
    tm.mkNullableSome(tm.mkBitVector(3, "101", 2))
    tm.mkNullableSome(tm.mkInteger("5"))
    tm.mkNullableSome(tm.mkReal("5.3"))

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkNullableSome(tm.mkBitVector(3, "101", 2))


def test_mk_nullable_val(tm, solver):
    some = tm.mkNullableSome(tm.mkInteger("5"))
    value = tm.mkNullableVal(some)
    value = solver.simplify(value)
    assert int(value.getIntegerValue()) == 5

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkNullableVal(tm.mkNullableSome(tm.mkBitVector(3, "101", 2)))


def test_mk_nullable_is_null(tm, solver):
    some = tm.mkNullableSome(tm.mkInteger("5"))
    value = tm.mkNullableIsNull(some)
    value = solver.simplify(value)
    assert not value.getBooleanValue()

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkNullableIsNull(tm.mkNullableSome(tm.mkInteger(5)))


def test_mk_nullable_is_some(tm, solver):
    some = tm.mkNullableSome(tm.mkInteger("5"))
    value = tm.mkNullableIsSome(some)
    value = solver.simplify(value)
    assert value.getBooleanValue()

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkNullableIsSome(tm.mkNullableSome(tm.mkInteger(5)))


def test_mk_nullable_null(tm, solver):
    nullable_sort = tm.mkNullableSort(tm.getBooleanSort())
    nullable_null = tm.mkNullableNull(nullable_sort)
    value = tm.mkNullableIsNull(nullable_null)
    value = solver.simplify(value)
    assert value.getBooleanValue()

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkNullableIsNull(
            tm.mkNullableNull(tm.mkNullableSort(tm.getBooleanSort())))


def test_mk_nullable_lift(tm, solver):
    some1 = tm.mkNullableSome(tm.mkInteger(1))
    some2 = tm.mkNullableSome(tm.mkInteger(2))
    some3 = tm.mkNullableLift(Kind.ADD, some1, some2)
    three = solver.simplify(tm.mkNullableVal(some3))
    assert int(three.getIntegerValue()) == 3

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkNullableLift(
            Kind.ADD,
            tm.mkNullableSome(
                tm.mkInteger(1)), tm.mkNullableSome(tm.mkInteger(2)))


def test_mk_universe_set(tm):
    tm.mkUniverseSet(tm.getBooleanSort())
    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkUniverseSet(tm.getBooleanSort())


def test_mk_const(tm):
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    funSort = tm.mkFunctionSort(intSort, boolSort)
    tm.mkConst(boolSort)
    tm.mkConst(funSort)
    tm.mkConst(boolSort, "b")
    tm.mkConst(intSort, "i")
    tm.mkConst(funSort, "f")
    tm.mkConst(funSort, "")

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkConst(boolSort)


def test_declare_fun_fresh(tm, solver):
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    t1 = solver.declareFun("b", [], boolSort, True)
    t2 = solver.declareFun("b", [], boolSort, False)
    t3 = solver.declareFun("b", [], boolSort, False)
    assert t1!=t2
    assert t1!=t3
    assert t2==t3
    t4 = solver.declareFun("c", [], boolSort, False)
    assert t2!=t4
    t5 = solver.declareFun("b", [], intSort, False)
    assert t2!=t5


def test_mk_const_array(tm):
    intSort = tm.getIntegerSort()
    arrSort = tm.mkArraySort(intSort, intSort)
    zero = tm.mkInteger(0)
    constArr = tm.mkConstArray(arrSort, zero)
    tm.mkConstArray(arrSort, zero)
    with pytest.raises(RuntimeError):
        tm.mkConstArray(arrSort, tm.mkBitVector(1, 1))
    with pytest.raises(RuntimeError):
        tm.mkConstArray(intSort, zero)

    ttm = TermManager()
    # this will throw when NodeManager is not a singleton anymore
    #with pytest.raises(RuntimeError):
    ttm.mkConstArray(arrSort, ttm.mkInteger(0))
    #with pytest.raises(RuntimeError):
    ttm.mkConstArray(ttm.mkArraySort(intSort, intSort), zero)


def test_uf_iteration(tm, solver):
    intSort = tm.getIntegerSort()
    funSort = tm.mkFunctionSort([intSort, intSort], intSort)
    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    f = tm.mkConst(funSort, "f")
    fxy = tm.mkTerm(Kind.APPLY_UF, f, x, y)

    # Expecting the uninterpreted function to be one of the children
    expected_children = [f, x, y]
    idx = 0
    for c in fxy:
        assert idx < 3
        assert c == expected_children[idx]
        idx = idx + 1


def test_get_statistics(tm, solver):
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
    stats = tm.getStatistics()
    assert stats['cvc5::TERM'] == {
            'default': False,
            'internal': False,
            'value': {'GEQ': 3, 'OR': 1}}
    assert stats.get(True, False) != {}

    for s in stats:
        if s[0] == 'cvc5::CONTANT':
            assert not s[1]['internal']
            assert not s[1]['default']
            assert s[1]['value'] == {'integer type': 1}
