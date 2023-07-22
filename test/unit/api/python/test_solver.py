###############################################################################
# Top contributors (to current version):
#   Ying Sheng, Yoni Zohar, Aina Niemetz
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
import sys

from cvc5 import Kind, SortKind, BlockModelsMode, RoundingMode, LearnedLitType, ProofComponent


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_recoverable_exception(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    with pytest.raises(RuntimeError):
        c = solver.getValue(x)


def test_supports_floating_point(solver):
    solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN)


def test_get_boolean_sort(solver):
    solver.getBooleanSort()


def test_get_integer_sort(solver):
    solver.getIntegerSort()


def test_get_real_sort(solver):
    solver.getRealSort()


def test_get_reg_exp_sort(solver):
    solver.getRegExpSort()


def test_get_string_sort(solver):
    solver.getStringSort()


def test_get_rounding_mode_sort(solver):
    solver.getRoundingModeSort()


def test_mk_array_sort(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    bvSort = solver.mkBitVectorSort(32)
    solver.mkArraySort(boolSort, boolSort)
    solver.mkArraySort(intSort, intSort)
    solver.mkArraySort(realSort, realSort)
    solver.mkArraySort(bvSort, bvSort)
    solver.mkArraySort(boolSort, intSort)
    solver.mkArraySort(realSort, bvSort)

    fpSort = solver.mkFloatingPointSort(3, 5)
    solver.mkArraySort(fpSort, fpSort)
    solver.mkArraySort(bvSort, fpSort)

    slv = cvc5.Solver()
    slv.mkArraySort(boolSort, boolSort)


def test_mk_bit_vector_sort(solver):
    solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        solver.mkBitVectorSort(0)


def test_mk_floating_point_sort(solver):
    solver.mkFloatingPointSort(4, 8)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPointSort(0, 8)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPointSort(4, 0)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPointSort(1, 8)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPointSort(4, 1)


def test_mk_datatype_sort(solver):
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    solver.mkDatatypeSort(dtypeSpec)

    with pytest.raises(RuntimeError):
        solver.mkDatatypeSort(dtypeSpec)
    slv = cvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSort(dtypeSpec)

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSort(throwsDtypeSpec)


def test_mk_datatype_sorts(solver):
    slv = cvc5.Solver()

    dtypeSpec1 = solver.mkDatatypeDecl("list1")
    cons1 = solver.mkDatatypeConstructorDecl("cons1")
    cons1.addSelector("head1", solver.getIntegerSort())
    dtypeSpec1.addConstructor(cons1)
    nil1 = solver.mkDatatypeConstructorDecl("nil1")
    dtypeSpec1.addConstructor(nil1)

    dtypeSpec2 = solver.mkDatatypeDecl("list2")
    cons2 = solver.mkDatatypeConstructorDecl("cons2")
    cons2.addSelector("head2", solver.getIntegerSort())
    dtypeSpec2.addConstructor(cons2)
    nil2 = solver.mkDatatypeConstructorDecl("nil2")
    dtypeSpec2.addConstructor(nil2)

    decls = [dtypeSpec1, dtypeSpec2]
    solver.mkDatatypeSorts(decls)

    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(decls)
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(decls)

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    throwsDecls = [throwsDtypeSpec]
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(throwsDecls)

    # with unresolved sorts
    unresList = solver.mkUnresolvedDatatypeSort("ulist")
    ulist = solver.mkDatatypeDecl("ulist")
    ucons = solver.mkDatatypeConstructorDecl("ucons")
    ucons.addSelector("car", unresList)
    ucons.addSelector("cdr", unresList)
    ulist.addConstructor(ucons)
    unil = solver.mkDatatypeConstructorDecl("unil")
    ulist.addConstructor(unil)
    udecls = [ulist]

    solver.mkDatatypeSorts(udecls)
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(udecls)
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(udecls)

    # mutually recursive with unresolved parameterized sorts
    p0 = solver.mkParamSort("p0")
    p1 = solver.mkParamSort("p1")
    u0 = solver.mkUnresolvedDatatypeSort("dt0", 1)
    u1 = solver.mkUnresolvedDatatypeSort("dt1", 1)
    dtdecl0 = solver.mkDatatypeDecl("dt0", [p0])
    dtdecl1 = solver.mkDatatypeDecl("dt1", [p1])
    ctordecl0 = solver.mkDatatypeConstructorDecl("c0")
    ctordecl0.addSelector("s0", u1.instantiate([p0]))
    ctordecl1 = solver.mkDatatypeConstructorDecl("c1")
    ctordecl1.addSelector("s1", u0.instantiate([p1]))
    dtdecl0.addConstructor(ctordecl0)
    dtdecl1.addConstructor(ctordecl1)
    dtdecl1.addConstructor(solver.mkDatatypeConstructorDecl("nil"))
    dt_sorts = solver.mkDatatypeSorts([dtdecl0, dtdecl1])
    isort1 = dt_sorts[1].instantiate([solver.getBooleanSort()])
    t1 = solver.mkConst(isort1, "t")
    t0 = solver.mkTerm(
        Kind.APPLY_SELECTOR,
        t1.getSort().getDatatype().getSelector("s1").getTerm(),
        t1)
    assert dt_sorts[0].instantiate([solver.getBooleanSort()]) == t0.getSort()

def test_mk_function_sort(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())

    # function arguments are allowed
    solver.mkFunctionSort(funSort, solver.getIntegerSort())

    # non-first-class arguments are not allowed
    reSort = solver.getRegExpSort()
    with pytest.raises(RuntimeError):
        solver.mkFunctionSort(reSort, solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkFunctionSort(solver.getIntegerSort(), funSort)

    solver.mkFunctionSort([solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort()],\
            solver.getIntegerSort())
    funSort2 = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())

    # function arguments are allowed
    solver.mkFunctionSort([funSort2, solver.mkUninterpretedSort("u")],\
            solver.getIntegerSort())

    with pytest.raises(RuntimeError):
        solver.mkFunctionSort([solver.getIntegerSort(),\
                solver.mkUninterpretedSort("u")],\
                funSort2)

    slv = cvc5.Solver()
    slv.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    slv.mkFunctionSort(slv.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    sorts1 = [solver.getBooleanSort(),\
            slv.getIntegerSort(),\
            solver.getIntegerSort()]
    sorts2 = [slv.getBooleanSort(), slv.getIntegerSort()]
    slv.mkFunctionSort(sorts2, slv.getIntegerSort())
    slv.mkFunctionSort(sorts1, slv.getIntegerSort())
    slv.mkFunctionSort(sorts2, solver.getIntegerSort())


def test_mk_param_sort(solver):
    solver.mkParamSort("T")
    solver.mkParamSort("")


def test_mk_predicate_sort(solver):
    solver.mkPredicateSort(solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkPredicateSort()

    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    # functions as arguments are allowed
    solver.mkPredicateSort(solver.getIntegerSort(), funSort)

    slv = cvc5.Solver()
    slv.mkPredicateSort(solver.getIntegerSort())


def test_mk_record_sort(solver):
    fields = [("b", solver.getBooleanSort()),\
              ("bv", solver.mkBitVectorSort(8)),\
              ("i", solver.getIntegerSort())]
    solver.mkRecordSort(*fields)
    solver.mkRecordSort()
    recSort = solver.mkRecordSort(*fields)
    recSort.getDatatype()


def test_mk_set_sort(solver):
    solver.mkSetSort(solver.getBooleanSort())
    solver.mkSetSort(solver.getIntegerSort())
    solver.mkSetSort(solver.mkBitVectorSort(4))
    slv = cvc5.Solver()
    slv.mkSetSort(solver.mkBitVectorSort(4))


def test_mk_bag_sort(solver):
    solver.mkBagSort(solver.getBooleanSort())
    solver.mkBagSort(solver.getIntegerSort())
    solver.mkBagSort(solver.mkBitVectorSort(4))
    slv = cvc5.Solver()
    slv.mkBagSort(solver.mkBitVectorSort(4))


def test_mk_sequence_sort(solver):
    solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkSequenceSort(\
            solver.mkSequenceSort(solver.getIntegerSort()))
    slv = cvc5.Solver()
    slv.mkSequenceSort(solver.getIntegerSort())



def test_mk_abstract_sort(solver):
    solver.mkAbstractSort(SortKind.ARRAY_SORT)
    solver.mkAbstractSort(SortKind.BITVECTOR_SORT)
    solver.mkAbstractSort(SortKind.TUPLE_SORT)
    solver.mkAbstractSort(SortKind.SET_SORT)
    with pytest.raises(RuntimeError):
        solver.mkAbstractSort(SortKind.BOOLEAN_SORT)


def test_mk_uninterpreted_sort(solver):
    solver.mkUninterpretedSort("u")
    solver.mkUninterpretedSort("")


def test_mk_unresolved_sort(solver):
    solver.mkUnresolvedDatatypeSort("u")
    solver.mkUnresolvedDatatypeSort("u", 1)
    solver.mkUnresolvedDatatypeSort("")
    solver.mkUnresolvedDatatypeSort("", 1)


def test_mk_sort_constructor_sort(solver):
    solver.mkUninterpretedSortConstructorSort(2, "s")
    solver.mkUninterpretedSortConstructorSort(2)
    with pytest.raises(RuntimeError):
        solver.mkUninterpretedSortConstructorSort(0)


def test_mk_tuple_sort(solver):
    solver.mkTupleSort(solver.getIntegerSort())
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    solver.mkTupleSort(solver.getIntegerSort(), funSort)

    slv = cvc5.Solver()
    slv.mkTupleSort(solver.getIntegerSort())


def test_mk_bit_vector(solver):
    solver.mkBitVector(8, 2)
    solver.mkBitVector(32, 2)

    solver.mkBitVector(4, "1010", 2)
    solver.mkBitVector(8, "0101", 2)
    solver.mkBitVector(8, "-1111111", 2)
    solver.mkBitVector(8, "00000101", 2)
    solver.mkBitVector(8, "-127", 10)
    solver.mkBitVector(8, "255", 10)
    solver.mkBitVector(10, "1010", 10)
    solver.mkBitVector(11, "1234", 10)
    solver.mkBitVector(8, "-7f", 16)
    solver.mkBitVector(8, "a0", 16)
    solver.mkBitVector(16, "1010", 16)
    solver.mkBitVector(16, "a09f", 16)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(0, 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(0, "-127", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(0, "a0", 16)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(2, "", 2)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "101", 5)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "127", 11)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "a0", 21)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "101010101", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-11111111", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-256", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "257", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-a0", 16)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "fffff", 16)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "10201010", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-25x", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "2x7", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "fzff", 16)

    assert solver.mkBitVector(8, "0101",
                              2) == solver.mkBitVector(8, "00000101", 2)
    assert solver.mkBitVector(4, "1010", 2) == solver.mkBitVector(4, "10", 10)
    assert solver.mkBitVector(4, "1010", 2) == solver.mkBitVector(4, "a", 16)
    assert str(solver.mkBitVector(8, "01010101", 2)) == "#b01010101"
    assert str(solver.mkBitVector(8, "F", 16)) == "#b00001111"
    assert solver.mkBitVector(8, "-1", 10) ==\
            solver.mkBitVector(8, "FF", 16)


def test_mk_var(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkVar(boolSort)
    solver.mkVar(funSort)
    solver.mkVar(boolSort, "b")
    solver.mkVar(funSort, "")
    with pytest.raises(RuntimeError):
        solver.mkVar(cvc5.Sort(solver))
    with pytest.raises(RuntimeError):
        solver.mkVar(cvc5.Sort(solver), "a")
    slv = cvc5.Solver()
    slv.mkVar(boolSort, "x")


def test_mk_boolean(solver):
    solver.mkBoolean(True)
    solver.mkBoolean(False)


def test_mk_rounding_mode(solver):
    assert str(solver.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN)) == "roundNearestTiesToEven"
    assert str(solver.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_POSITIVE)) == "roundTowardPositive"
    assert str(solver.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_NEGATIVE)) == "roundTowardNegative"
    assert str(solver.mkRoundingMode(
        RoundingMode.ROUND_TOWARD_ZERO)) == "roundTowardZero"
    assert str(solver.mkRoundingMode(
        RoundingMode.ROUND_NEAREST_TIES_TO_AWAY)) == "roundNearestTiesToAway"


def test_mk_floating_point(solver):
    t1 = solver.mkBitVector(8)
    t2 = solver.mkBitVector(4)
    t3 = solver.mkInteger(2)
    solver.mkFloatingPoint(3, 5, t1)

    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(0, 5, cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(0, 5, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 0, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)

    sign = solver.mkBitVector(1)
    exp = solver.mkBitVector(5)
    sig = solver.mkBitVector(10)
    bv = solver.mkBitVector(16)
    a = solver.mkFloatingPoint(
            sign, exp, sig)
    assert solver.mkFloatingPoint(
            sign, exp, sig) == solver.mkFloatingPoint(5, 11, bv)
    slv = cvc5.Solver()
    slv.mkFloatingPoint(3, 5, t1)


def test_mk_cardinality_constraint(solver):
    su = solver.mkUninterpretedSort("u")
    si = solver.getIntegerSort()
    solver.mkCardinalityConstraint(su, 3)
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.mkCardinalityConstraint(si, 3))
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.mkCardinalityConstraint(su, 0))
    slv = cvc5.Solver()
    slv.mkCardinalityConstraint(su, 3)


def test_mk_empty_set(solver):
    slv = cvc5.Solver()
    s = solver.mkSetSort(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(cvc5.Sort(solver))
    solver.mkEmptySet(s)
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.getBooleanSort())
    slv.mkEmptySet(s)


def test_mk_empty_bag(solver):
    slv = cvc5.Solver()
    s = solver.mkBagSort(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkEmptyBag(cvc5.Sort(solver))
    solver.mkEmptyBag(s)
    with pytest.raises(RuntimeError):
        solver.mkEmptyBag(solver.getBooleanSort())
    slv.mkEmptyBag(s)


def test_mk_empty_sequence(solver):
    slv = cvc5.Solver()
    s = solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkEmptySequence(s)
    solver.mkEmptySequence(solver.getBooleanSort())
    slv.mkEmptySequence(s)


def test_mk_false(solver):
    solver.mkFalse()
    solver.mkFalse()


def test_mk_floating_point_nan(solver):
    solver.mkFloatingPointNaN(3, 5)


def test_mk_floating_point_neg_zero(solver):
    solver.mkFloatingPointNegZero(3, 5)


def test_mk_floating_point_neg_inf(solver):
    solver.mkFloatingPointNegInf(3, 5)


def test_mk_floating_point_pos_inf(solver):
    solver.mkFloatingPointPosInf(3, 5)


def test_mk_floating_point_pos_zero(solver):
    solver.mkFloatingPointPosZero(3, 5)


def test_mk_op(solver):
    with pytest.raises(ValueError):
        solver.mkOp(Kind.BITVECTOR_EXTRACT, Kind.EQUAL)

    solver.mkOp(Kind.DIVISIBLE, "2147483648")
    with pytest.raises(RuntimeError):
        solver.mkOp(Kind.BITVECTOR_EXTRACT, "asdf")

    solver.mkOp(Kind.DIVISIBLE, 1)
    solver.mkOp(Kind.BITVECTOR_ROTATE_LEFT, 1)
    solver.mkOp(Kind.BITVECTOR_ROTATE_RIGHT, 1)
    with pytest.raises(RuntimeError):
        solver.mkOp(Kind.BITVECTOR_EXTRACT, 1)

    solver.mkOp(Kind.BITVECTOR_EXTRACT, 1, 1)
    with pytest.raises(RuntimeError):
        solver.mkOp(Kind.DIVISIBLE, 1, 2)

    args = [1, 2, 2]
    solver.mkOp(Kind.TUPLE_PROJECT, *args)


def test_mk_pi(solver):
    solver.mkPi()


def test_mk_integer(solver):
    solver.mkInteger("123")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".2")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2.")
    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/2")

    solver.mkReal("123")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".2")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2.")
    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    solver.mkInteger(val1)
    solver.mkInteger(val2)
    solver.mkInteger(val3)
    solver.mkInteger(val4)
    solver.mkInteger(val4)


def test_mk_real(solver):
    solver.mkReal("123")
    solver.mkReal("1.23")
    solver.mkReal("1/23")
    solver.mkReal("12/3")
    solver.mkReal(".2")
    solver.mkReal("2.")
    with pytest.raises(RuntimeError):
        solver.mkReal("")
    with pytest.raises(RuntimeError):
        solver.mkReal("asdf")
    with pytest.raises(RuntimeError):
        solver.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkReal(".")
    with pytest.raises(RuntimeError):
        solver.mkReal("/")
    with pytest.raises(RuntimeError):
        solver.mkReal("2/")
    with pytest.raises(RuntimeError):
        solver.mkReal("/2")

    solver.mkReal("123")
    solver.mkReal("1.23")
    solver.mkReal("1/23")
    solver.mkReal("12/3")
    solver.mkReal(".2")
    solver.mkReal("2.")
    with pytest.raises(RuntimeError):
        solver.mkReal("")
    with pytest.raises(RuntimeError):
        solver.mkReal("asdf")
    with pytest.raises(RuntimeError):
        solver.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkReal(".")
    with pytest.raises(RuntimeError):
        solver.mkReal("/")
    with pytest.raises(RuntimeError):
        solver.mkReal("2/")
    with pytest.raises(RuntimeError):
        solver.mkReal("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    solver.mkReal(val1)
    solver.mkReal(val2)
    solver.mkReal(val3)
    solver.mkReal(val4)
    solver.mkReal(val4)
    solver.mkReal(val1, val1)
    solver.mkReal(val2, val2)
    solver.mkReal(val3, val3)
    solver.mkReal(val4, val4)

    solver.mkReal("1", "2")
    solver.mkReal("-1", "2")
    solver.mkReal(-1, "2")
    solver.mkReal("-1", 2)
    with pytest.raises(TypeError):
        solver.mkReal(1, 2, 3)
    with pytest.raises(RuntimeError):
        solver.mkReal("1.0", 2)
    with pytest.raises(RuntimeError):
        solver.mkReal(1, "asdf")


def test_mk_regexp_none(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(Kind.STRING_IN_REGEXP, s, solver.mkRegexpNone())


def test_mk_regexp_all(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(Kind.STRING_IN_REGEXP, s, solver.mkRegexpAll())


def test_mk_regexp_allchar(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(Kind.STRING_IN_REGEXP, s, solver.mkRegexpAllchar())


def test_mk_sep_emp(solver):
    solver.mkSepEmp()


def test_mk_sep_nil(solver):
    solver.mkSepNil(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkSepNil(cvc5.Sort(solver))
    slv = cvc5.Solver()
    slv.mkSepNil(solver.getIntegerSort())


def test_mk_string(solver):
    solver.mkString("")
    solver.mkString("asdfasdf")
    str(solver.mkString("asdf\\nasdf")) == "\"asdf\\u{5c}nasdf\""
    str(solver.mkString("asdf\\u{005c}nasdf", True)) ==\
            "\"asdf\\u{5c}nasdf\""
    s = ""
    assert solver.mkString(s).getStringValue() == s


def test_mk_term(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    b = solver.mkConst(bv32, "b")
    slv = cvc5.Solver()

    # mkTerm(Kind kind) const
    solver.mkPi()
    solver.mkTerm(Kind.PI)
    solver.mkTerm(solver.mkOp(Kind.PI))
    solver.mkTerm(Kind.REGEXP_NONE)
    solver.mkTerm(solver.mkOp(Kind.REGEXP_NONE))
    solver.mkTerm(Kind.REGEXP_ALLCHAR)
    solver.mkTerm(solver.mkOp(Kind.REGEXP_ALLCHAR))
    solver.mkTerm(Kind.SEP_EMP)
    solver.mkTerm(solver.mkOp(Kind.SEP_EMP))
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.CONST_BITVECTOR)

    # mkTerm(Kind kind, Term child) const
    solver.mkTerm(Kind.NOT, solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.NOT, cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.NOT, a)
    slv.mkTerm(Kind.NOT, solver.mkTrue())

    # mkTerm(Kind kind, Term child1, Term child2) const
    solver.mkTerm(Kind.EQUAL, a, b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.EQUAL, cvc5.Term(solver), b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.EQUAL, a, cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.EQUAL, a, solver.mkTrue())
    slv.mkTerm(Kind.EQUAL, a, b)

    # mkTerm(Kind kind, Term child1, Term child2, Term child3) const
    solver.mkTerm(Kind.ITE, solver.mkTrue(), solver.mkTrue(), solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.ITE, cvc5.Term(solver), solver.mkTrue(),
                      solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.ITE, solver.mkTrue(), cvc5.Term(solver),
                      solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.ITE, solver.mkTrue(), solver.mkTrue(),
                      cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.ITE, solver.mkTrue(), solver.mkTrue(), b)
    slv.mkTerm(Kind.ITE, solver.mkTrue(), solver.mkTrue(),
               solver.mkTrue())

    solver.mkTerm(Kind.EQUAL, a, b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.EQUAL, a, cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.EQUAL, a, solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.DISTINCT)

    # Test cases that are nary via the API but have arity = 2 internally
    s_bool = solver.getBooleanSort()
    t_bool = solver.mkConst(s_bool, "t_bool")
    solver.mkTerm(Kind.IMPLIES, t_bool, t_bool, t_bool)
    solver.mkTerm(Kind.XOR, t_bool, t_bool, t_bool)
    solver.mkTerm(solver.mkOp(Kind.XOR), t_bool, t_bool, t_bool)
    t_int = solver.mkConst(solver.getIntegerSort(), "t_int")
    solver.mkTerm(Kind.DIVISION, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.DIVISION), t_int, t_int, t_int)
    solver.mkTerm(Kind.INTS_DIVISION, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.INTS_DIVISION), t_int, t_int, t_int)
    solver.mkTerm(Kind.SUB, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.SUB), t_int, t_int, t_int)
    solver.mkTerm(Kind.EQUAL, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.EQUAL), t_int, t_int, t_int)
    solver.mkTerm(Kind.LT, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.LT), t_int, t_int, t_int)
    solver.mkTerm(Kind.GT, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.GT), t_int, t_int, t_int)
    solver.mkTerm(Kind.LEQ, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.LEQ), t_int, t_int, t_int)
    solver.mkTerm(Kind.GEQ, t_int, t_int, t_int)
    solver.mkTerm(solver.mkOp(Kind.GEQ), t_int, t_int, t_int)
    t_reg = solver.mkConst(solver.getRegExpSort(), "t_reg")
    solver.mkTerm(Kind.REGEXP_DIFF, t_reg, t_reg, t_reg)
    solver.mkTerm(solver.mkOp(Kind.REGEXP_DIFF), t_reg, t_reg, t_reg)
    t_fun = solver.mkConst(solver.mkFunctionSort(
        [s_bool, s_bool, s_bool], s_bool))
    solver.mkTerm(Kind.HO_APPLY, t_fun, t_bool, t_bool, t_bool)
    solver.mkTerm(solver.mkOp(Kind.HO_APPLY), t_fun, t_bool, t_bool, t_bool)
    

def test_mk_term_from_op(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    b = solver.mkConst(bv32, "b")
    slv = cvc5.Solver()

    # simple operator terms
    opterm1 = solver.mkOp(Kind.BITVECTOR_EXTRACT, 2, 1)
    opterm2 = solver.mkOp(Kind.DIVISIBLE, 1)

    # list datatype
    sort = solver.mkParamSort("T")
    listDecl = solver.mkDatatypeDecl("paramlist", [sort])
    cons = solver.mkDatatypeConstructorDecl("cons")
    nil = solver.mkDatatypeConstructorDecl("nil")
    cons.addSelector("head", sort)
    cons.addSelectorSelf("tail")
    listDecl.addConstructor(cons)
    listDecl.addConstructor(nil)
    listSort = solver.mkDatatypeSort(listDecl)
    intListSort =\
        listSort.instantiate([solver.getIntegerSort()])
    c = solver.mkConst(intListSort, "c")
    lis = listSort.getDatatype()

    # list datatype constructor and selector operator terms
    consTerm = lis.getConstructor("cons").getTerm()
    nilTerm = lis.getConstructor("nil").getTerm()
    headTerm = lis["cons"].getSelector("head").getTerm()
    tailTerm = lis["cons"]["tail"].getTerm()

    # mkTerm(Op op, Term term) const
    solver.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm)
    solver.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.APPLY_SELECTOR, nilTerm)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.APPLY_SELECTOR, consTerm)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.APPLY_SELECTOR, headTerm)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1)
    slv.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm)

    # mkTerm(Op op, Term child) const
    solver.mkTerm(opterm1, a)
    solver.mkTerm(opterm2, solver.mkInteger(1))
    solver.mkTerm(Kind.APPLY_SELECTOR, headTerm, c)
    solver.mkTerm(Kind.APPLY_SELECTOR, tailTerm, c)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, a)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1, cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm, solver.mkInteger(0))
    slv.mkTerm(opterm1, a)

    # mkTerm(Op op, Term child1, Term child2) const
    solver.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm, solver.mkInteger(0),
                  solver.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), solver.mkInteger(2))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1, a, b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, cvc5.Term(solver), solver.mkInteger(1))
    slv.mkTerm(Kind.APPLY_CONSTRUCTOR,\
                    consTerm,\
                    solver.mkInteger(0),\
                    solver.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm))

    # mkTerm(Op op, Term child1, Term child2, Term child3) const
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1, a, b, a)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), solver.mkInteger(1),
                      cvc5.Term(solver))

    solver.mkTerm(opterm2, solver.mkInteger(5))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), solver.mkInteger(2))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2)
    slv.mkTerm(opterm2, solver.mkInteger(5))


def test_mk_true(solver):
    solver.mkTrue()
    solver.mkTrue()


def test_mk_tuple(solver):
    solver.mkTuple([solver.mkBitVector(3, "101", 2)])
    solver.mkTuple([solver.mkInteger("5")])
    solver.mkTuple([solver.mkReal("5.3")])
    slv = cvc5.Solver()
    slv.mkTuple([slv.mkBitVector(3, "101", 2)])
    slv.mkTuple([solver.mkBitVector(3, "101", 2)])


def test_mk_universe_set(solver):
    solver.mkUniverseSet(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkUniverseSet(cvc5.Sort(solver))
    slv = cvc5.Solver()
    slv.mkUniverseSet(solver.getBooleanSort())


def test_mk_const(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkConst(boolSort)
    solver.mkConst(funSort)
    solver.mkConst(boolSort, "b")
    solver.mkConst(intSort, "i")
    solver.mkConst(funSort, "f")
    solver.mkConst(funSort, "")
    with pytest.raises(RuntimeError):
        solver.mkConst(cvc5.Sort(solver))
    with pytest.raises(RuntimeError):
        solver.mkConst(cvc5.Sort(solver), "a")

    slv = cvc5.Solver()
    slv.mkConst(boolSort)


def test_mk_const_array(solver):
    intSort = solver.getIntegerSort()
    arrSort = solver.mkArraySort(intSort, intSort)
    zero = solver.mkInteger(0)
    constArr = solver.mkConstArray(arrSort, zero)

    solver.mkConstArray(arrSort, zero)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(cvc5.Sort(solver), zero)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, solver.mkBitVector(1, 1))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(intSort, zero)
    slv = cvc5.Solver()
    zero2 = slv.mkInteger(0)
    arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort())
    slv.mkConstArray(arrSort2, zero)
    slv.mkConstArray(arrSort, zero2)


def test_declare_fun(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    solver.declareFun("f1", [], bvSort)
    solver.declareFun("f3", [bvSort, solver.getIntegerSort()], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f2", [], funSort)
    # functions as arguments is allowed
    solver.declareFun("f4", [bvSort, funSort], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f5", [bvSort, bvSort], funSort)
    slv = cvc5.Solver()
    slv.declareFun("f1", [], bvSort)


def test_declare_sort(solver):
    solver.declareSort("s", 0)
    solver.declareSort("s", 2)
    solver.declareSort("", 2)


def test_define_fun(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    b1 = solver.mkVar(bvSort, "b1")
    b2 = solver.mkVar(solver.getIntegerSort(), "b2")
    b3 = solver.mkVar(funSort, "b3")
    v1 = solver.mkConst(bvSort, "v1")
    v2 = solver.mkConst(funSort, "v2")
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

    slv = cvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    slv.defineFun("f", [], bvSort, v12)
    slv.defineFun("f", [], bvSort2, v1)
    slv.defineFun("ff", [b1, b22], bvSort2, v12)
    slv.defineFun("ff", [b12, b2], bvSort2, v12)
    slv.defineFun("ff", [b12, b22], bvSort, v12)
    slv.defineFun("ff", [b12, b22], bvSort2, v1)


def test_define_fun_global(solver):
    bSort = solver.getBooleanSort()

    bTrue = solver.mkBoolean(True)
    # (define-fun f () Bool true)
    f = solver.defineFun("f", [], bSort, bTrue, True)
    b = solver.mkVar(bSort, "b")
    # (define-fun g (b Bool) Bool b)
    g = solver.defineFun("g", [b], bSort, b, True)

    # (assert (or (not f) (not (g true))))
    solver.assertFormula(
        solver.mkTerm(Kind.OR, f.notTerm(),
                      solver.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
    assert solver.checkSat().isUnsat()
    solver.resetAssertions()
    # (assert (or (not f) (not (g true))))
    solver.assertFormula(
        solver.mkTerm(Kind.OR, f.notTerm(),
                      solver.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
    assert solver.checkSat().isUnsat()


def test_define_fun_rec(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                     solver.getIntegerSort())
    b1 = solver.mkVar(bvSort, "b1")
    b11 = solver.mkVar(bvSort, "b1")
    b2 = solver.mkVar(solver.getIntegerSort(), "b2")
    b3 = solver.mkVar(funSort2, "b3")
    v1 = solver.mkConst(bvSort, "v1")
    v2 = solver.mkConst(solver.getIntegerSort(), "v2")
    v3 = solver.mkConst(funSort2, "v3")
    f1 = solver.mkConst(funSort1, "f1")
    f2 = solver.mkConst(funSort2, "f2")
    f3 = solver.mkConst(bvSort, "f3")
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

    slv = cvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    slv.defineFunRec("f", [], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort2, v12)
    slv.defineFunRec("f", [], bvSort, v12)
    slv.defineFunRec("f", [], bvSort2, v1)
    slv.defineFunRec("ff", [b1, b22], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b2], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort2, v1)


def test_define_fun_rec_wrong_logic(solver):
    solver.setLogic("QF_BV")
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    b = solver.mkVar(bvSort, "b")
    v = solver.mkConst(bvSort, "v")
    f = solver.mkConst(funSort, "f")
    with pytest.raises(RuntimeError):
        solver.defineFunRec("f", [], bvSort, v)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f, [b, b], v)


def test_define_fun_rec_global(solver):
  bSort = solver.getBooleanSort()
  fSort = solver.mkFunctionSort([bSort], bSort)

  solver.push()
  bTrue = solver.mkBoolean(True)
  # (define-fun f () Bool true)
  f = solver.defineFunRec("f", [], bSort, bTrue, True)
  b = solver.mkVar(bSort, "b")
  gSym = solver.mkConst(fSort, "g")
  # (define-fun g (b Bool) Bool b)
  g = solver.defineFunRec(gSym, [b], b, glbl=True)

  # (assert (or (not f) (not (g true))))
  solver.assertFormula(solver.mkTerm(
      Kind.OR, f.notTerm(), solver.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
  assert solver.checkSat().isUnsat()
  solver.pop()
  # (assert (or (not f) (not (g true))))
  solver.assertFormula(solver.mkTerm(
      Kind.OR, f.notTerm(), solver.mkTerm(Kind.APPLY_UF, g, bTrue).notTerm()))
  assert solver.checkSat().isUnsat()


def test_define_funs_rec(solver):
  uSort = solver.mkUninterpretedSort("u")
  bvSort = solver.mkBitVectorSort(32)
  funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
  funSort2 = solver.mkFunctionSort([uSort], solver.getIntegerSort())
  b1 = solver.mkVar(bvSort, "b1")
  b11 = solver.mkVar(bvSort, "b1")
  b2 = solver.mkVar(solver.getIntegerSort(), "b2")
  b3 = solver.mkVar(funSort2, "b3")
  b4 = solver.mkVar(uSort, "b4")
  v1 = solver.mkConst(bvSort, "v1")
  v2 = solver.mkConst(solver.getIntegerSort(), "v2")
  v3 = solver.mkConst(funSort2, "v3")
  v4 = solver.mkConst(uSort, "v4")
  f1 = solver.mkConst(funSort1, "f1")
  f2 = solver.mkConst(funSort2, "f2")
  f3 = solver.mkConst(bvSort, "f3")
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

  slv = cvc5.Solver()
  uSort2 = slv.mkUninterpretedSort("u")
  bvSort2 = slv.mkBitVectorSort(32)
  funSort12 = slv.mkFunctionSort([bvSort2, bvSort2], bvSort2)
  funSort22 = slv.mkFunctionSort([uSort2], slv.getIntegerSort())
  b12 = slv.mkVar(bvSort2, "b1")
  b112 = slv.mkVar(bvSort2, "b1")
  b42 = slv.mkVar(uSort2, "b4")
  v12 = slv.mkConst(bvSort2, "v1")
  v22 = slv.mkConst(slv.getIntegerSort(), "v2")
  f12 = slv.mkConst(funSort12, "f1")
  f22 = slv.mkConst(funSort22, "f2")

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


def test_define_funs_rec_wrong_logic(solver):
  solver.setLogic("QF_BV")
  uSort = solver.mkUninterpretedSort("u")
  bvSort = solver.mkBitVectorSort(32)
  funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
  funSort2 = solver.mkFunctionSort([uSort], solver.getIntegerSort())
  b = solver.mkVar(bvSort, "b")
  u = solver.mkVar(uSort, "u")
  v1 = solver.mkConst(bvSort, "v1")
  v2 = solver.mkConst(solver.getIntegerSort(), "v2")
  f1 = solver.mkConst(funSort1, "f1")
  f2 = solver.mkConst(funSort2, "f2")
  with pytest.raises(RuntimeError):
    solver.defineFunsRec([f1, f2], [[b, b], [u]], [v1, v2])


def test_define_funs_rec_global(solver):
  bSort = solver.getBooleanSort()
  fSort = solver.mkFunctionSort([bSort], bSort)

  solver.push()
  bTrue = solver.mkBoolean(True)
  b = solver.mkVar(bSort, "b")
  gSym = solver.mkConst(fSort, "g")
  # (define-funs-rec ((g ((b Bool)) Bool)) (b))
  solver.defineFunsRec([gSym], [[b]], [b], True)

  # (assert (not (g true)))
  solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, gSym, bTrue).notTerm())
  assert solver.checkSat().isUnsat()
  solver.pop()
  # (assert (not (g true)))
  solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, gSym, bTrue).notTerm())
  assert solver.checkSat().isUnsat()


def test_uf_iteration(solver):
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort([intSort, intSort], intSort)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    f = solver.mkConst(funSort, "f")
    fxy = solver.mkTerm(Kind.APPLY_UF, f, x, y)

    # Expecting the uninterpreted function to be one of the children
    expected_children = [f, x, y]
    idx = 0
    for c in fxy:
        assert idx < 3
        assert c == expected_children[idx]
        idx = idx + 1


def test_get_assertions(solver):
    a = solver.mkConst(solver.getBooleanSort(), 'a')
    b = solver.mkConst(solver.getBooleanSort(), 'b')
    solver.assertFormula(a)
    solver.assertFormula(b)
    asserts = [a,b]
    assert solver.getAssertions() == asserts


def test_get_info(solver):
    solver.getInfo("name")
    with pytest.raises(RuntimeError):
        solver.getInfo("asdf")


def test_get_op(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    ext = solver.mkOp(Kind.BITVECTOR_EXTRACT, 2, 1)
    exta = solver.mkTerm(ext, a)

    assert not a.hasOp()
    with pytest.raises(RuntimeError):
        a.getOp()
    assert exta.hasOp()
    assert exta.getOp() == ext

    # Test Datatypes -- more complicated
    consListSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    cons.addSelectorSelf("tail")
    consListSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    consListSpec.addConstructor(nil)
    consListSort = solver.mkDatatypeSort(consListSpec)
    consList = consListSort.getDatatype()

    consTerm = consList.getConstructor("cons").getTerm()
    nilTerm = consList.getConstructor("nil").getTerm()
    headTerm = consList["cons"].getSelector("head").getTerm()

    listnil = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, nilTerm)
    listcons1 = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, consTerm,
                              solver.mkInteger(1), listnil)
    listhead = solver.mkTerm(Kind.APPLY_SELECTOR, headTerm, listcons1)

    assert listnil.hasOp()
    assert listcons1.hasOp()
    assert listhead.hasOp()


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


def test_get_unsat_core_and_proof(solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-cores", "true")
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

    unsat_core = solver.getUnsatCore()
    
    solver.getProof()
    solver.getProof(ProofComponent.PROOF_COMPONENT_SAT)

    solver.resetAssertions()
    for t in unsat_core:
        solver.assertFormula(t)
    res = solver.checkSat()
    assert res.isUnsat()
    solver.getProof()

def test_learned_literals(solver):
    solver.setOption("produce-learned-literals", "true")
    with pytest.raises(RuntimeError):
        solver.getLearnedLiterals()
    solver.checkSat()
    solver.getLearnedLiterals()
    solver.getLearnedLiterals(LearnedLitType.LEARNED_LIT_PREPROCESS)

def test_learned_literals2(solver):
    solver.setOption("produce-learned-literals", "true")
    intSort = solver.getIntegerSort()
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    zero = solver.mkInteger(0)
    ten = solver.mkInteger(10)
    f0 = solver.mkTerm(Kind.GEQ, x, ten)
    f1 = solver.mkTerm(
            Kind.OR,
            solver.mkTerm(Kind.GEQ, zero, x),
            solver.mkTerm(Kind.GEQ, y, zero))
    solver.assertFormula(f0)
    solver.assertFormula(f1)
    solver.checkSat()
    solver.getLearnedLiterals(LearnedLitType.LEARNED_LIT_INPUT)

def test_get_timeout_core_unsat(solver):
  solver.setOption("timeout-core-timeout", "100")
  solver.setOption("produce-unsat-cores", "true")
  intSort = solver.getIntegerSort()
  x = solver.mkConst(intSort, "x")
  tt = solver.mkBoolean(True)
  hard = solver.mkTerm(Kind.EQUAL,
                       solver.mkTerm(Kind.MULT, x, x),
                       solver.mkInteger("501240912901901249014210220059591"))
  solver.assertFormula(tt)
  solver.assertFormula(hard)
  res = solver.getTimeoutCore()
  assert res[0].isUnknown()
  assert len(res[1]) == 1
  assert res[1][0] == hard

def test_get_timeout_core(solver):
  solver.setOption("produce-unsat-cores", "true")
  ff = solver.mkBoolean(False)
  tt = solver.mkBoolean(True)
  solver.assertFormula(tt)
  solver.assertFormula(ff)
  solver.assertFormula(tt)
  res = solver.getTimeoutCore()
  assert res[0].isUnsat()
  assert len(res[1]) == 1
  assert res[1][0] == ff

def test_get_value1(solver):
    solver.setOption("produce-models", "false")
    t = solver.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValue(t)


def test_get_value2(solver):
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValue(t)


def test_get_value3(solver):
    solver.setOption("produce-models", "true")
    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    z = solver.mkConst(uSort, "z")
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    f_y = solver.mkTerm(Kind.APPLY_UF, f, y)
    summ = solver.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = solver.mkTerm(Kind.APPLY_UF, p, f_y)

    solver.assertFormula(solver.mkTerm(Kind.LEQ, zero, f_x))
    solver.assertFormula(solver.mkTerm(Kind.LEQ, zero, f_y))
    solver.assertFormula(solver.mkTerm(Kind.LEQ, summ, one))
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

    slv = cvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.getValue(x)


def test_declare_sep_heap(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    integer = solver.getIntegerSort()
    solver.declareSepHeap(integer, integer)
    # cannot declare separation logic heap more than once
    with pytest.raises(RuntimeError):
        solver.declareSepHeap(integer, integer)


# Helper function for test_get_separation_{heap,nil}_termX. Asserts and checks
# some simple separation logic constraints.
def checkSimpleSeparationConstraints(slv):
    integer = slv.getIntegerSort()
    # declare the separation heap
    slv.declareSepHeap(integer, integer)
    x = slv.mkConst(integer, "x")
    p = slv.mkConst(integer, "p")
    heap = slv.mkTerm(Kind.SEP_PTO, p, x)
    slv.assertFormula(heap)
    nil = slv.mkSepNil(integer)
    slv.assertFormula(nil.eqTerm(slv.mkInteger(5)))
    slv.checkSat()


def test_get_value_sep_heap_1(solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_get_value_sep_heap_3(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_4(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_get_value_sep_nil_1(solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_get_value_sep_nil_3(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_4(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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

def test_block_model1(solver):
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.blockModel(BlockModelsMode.LITERALS)

def test_block_model2(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    with pytest.raises(RuntimeError):
        solver.blockModel(BlockModelsMode.LITERALS)

def test_block_model3(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x");
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    solver.blockModel(BlockModelsMode.LITERALS)

def test_block_model_values1(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x");
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.blockModelValues([])
    with pytest.raises(RuntimeError):
        solver.blockModelValues([cvc5.Term(solver)])
    solver.blockModelValues([cvc5.Solver().mkBoolean(False)])

def test_block_model_values2(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    solver.blockModelValues([x])

def test_block_model_values3(solver):
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.blockModelValues([x])

def test_block_model_values4(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    with pytest.raises(RuntimeError):
        solver.blockModelValues([x])

def test_block_model_values5(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x))
    solver.checkSat()
    solver.blockModelValues([x])

def test_get_instantiations(solver):
    iSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    p = solver.declareFun("p", [iSort], boolSort)
    x = solver.mkVar(iSort, "x")
    bvl = solver.mkTerm(Kind.VARIABLE_LIST, x)
    app = solver.mkTerm(Kind.APPLY_UF, p, x)
    q = solver.mkTerm(Kind.FORALL, bvl, app)
    solver.assertFormula(q)
    five = solver.mkInteger(5)
    app2 = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, p, five))
    solver.assertFormula(app2)
    with pytest.raises(RuntimeError):
        solver.getInstantiations()
    solver.checkSat()
    solver.getInstantiations()

def test_get_statistics(solver):
    intSort = solver.getIntegerSort()
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    zero = solver.mkInteger(0)
    ten = solver.mkInteger(10)
    f0 = solver.mkTerm(Kind.GEQ, x, ten)
    f1 = solver.mkTerm(
            Kind.OR,
            solver.mkTerm(Kind.GEQ, zero, x),
            solver.mkTerm(Kind.GEQ, y, zero))
    solver.assertFormula(f0)
    solver.assertFormula(f1)
    solver.checkSat()
    s = solver.getStatistics()
    assert s['cvc5::TERM'] == {'defaulted': False, 'internal': False, 'value': {'GEQ': 3, 'OR': 1}}
    assert s.get(True, False) != {}

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


def test_simplify(solver):
    with pytest.raises(RuntimeError):
        solver.simplify(cvc5.Term(solver))

    bvSort = solver.mkBitVectorSort(32)
    uSort = solver.mkUninterpretedSort("u")
    funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = solver.mkFunctionSort(uSort, solver.getIntegerSort())
    consListSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    cons.addSelectorSelf("tail")
    consListSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    consListSpec.addConstructor(nil)
    consListSort = solver.mkDatatypeSort(consListSpec)

    x = solver.mkConst(bvSort, "x")
    solver.simplify(x)
    a = solver.mkConst(bvSort, "a")
    solver.simplify(a)
    b = solver.mkConst(bvSort, "b")
    solver.simplify(b)
    x_eq_x = solver.mkTerm(Kind.EQUAL, x, x)
    solver.simplify(x_eq_x)
    assert solver.mkTrue() != x_eq_x
    assert solver.mkTrue() == solver.simplify(x_eq_x)
    x_eq_b = solver.mkTerm(Kind.EQUAL, x, b)
    solver.simplify(x_eq_b)
    assert solver.mkTrue() != x_eq_b
    assert solver.mkTrue() != solver.simplify(x_eq_b)
    slv = cvc5.Solver()
    slv.simplify(x)

    i1 = solver.mkConst(solver.getIntegerSort(), "i1")
    solver.simplify(i1)
    i2 = solver.mkTerm(Kind.MULT, i1, solver.mkInteger("23"))
    solver.simplify(i2)
    assert i1 != i2
    assert i1 != solver.simplify(i2)
    i3 = solver.mkTerm(Kind.ADD, i1, solver.mkInteger(0))
    solver.simplify(i3)
    assert i1 != i3
    assert i1 == solver.simplify(i3)

    consList = consListSort.getDatatype()
    dt1 = solver.mkTerm(
        Kind.APPLY_CONSTRUCTOR,
        consList.getConstructor("cons").getTerm(),
        solver.mkInteger(0),
        solver.mkTerm(
            Kind.APPLY_CONSTRUCTOR,
            consList.getConstructor("nil").getTerm()))
    solver.simplify(dt1)
    dt2 = solver.mkTerm(
      Kind.APPLY_SELECTOR,
      consList["cons"].getSelector("head").getTerm(),
      dt1)
    solver.simplify(dt2)

    b1 = solver.mkVar(bvSort, "b1")
    solver.simplify(b1)
    b2 = solver.mkVar(bvSort, "b1")
    solver.simplify(b2)
    b3 = solver.mkVar(uSort, "b3")
    solver.simplify(b3)
    v1 = solver.mkConst(bvSort, "v1")
    solver.simplify(v1)
    v2 = solver.mkConst(solver.getIntegerSort(), "v2")
    solver.simplify(v2)
    f1 = solver.mkConst(funSort1, "f1")
    solver.simplify(f1)
    f2 = solver.mkConst(funSort2, "f2")
    solver.simplify(f2)
    solver.defineFunsRec([f1, f2], [[b1, b2], [b3]], [v1, v2])
    solver.simplify(f1)
    solver.simplify(f2)


def test_assert_formula(solver):
    solver.assertFormula(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.assertFormula(cvc5.Term(solver))
    slv = cvc5.Solver()
    slv.assertFormula(solver.mkTrue())


def test_check_sat(solver):
    solver.setOption("incremental", "false")
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.checkSat()


def test_check_sat_assuming(solver):
    solver.setOption("incremental", "false")
    solver.checkSatAssuming(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(solver.mkTrue())
    slv = cvc5.Solver()
    slv.checkSatAssuming(solver.mkTrue())


def test_check_sat_assuming1(solver):
    boolSort = solver.getBooleanSort()
    x = solver.mkConst(boolSort, "x")
    y = solver.mkConst(boolSort, "y")
    z = solver.mkTerm(Kind.AND, x, y)
    solver.setOption("incremental", "true")
    solver.checkSatAssuming(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(cvc5.Term(solver))
    solver.checkSatAssuming(solver.mkTrue())
    solver.checkSatAssuming(z)
    slv = cvc5.Solver()
    slv.checkSatAssuming(solver.mkTrue())


def test_check_sat_assuming2(solver):
    solver.setOption("incremental", "true")

    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    n = cvc5.Term(solver)
    # Constants
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    # Functions
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    # Values
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    # Terms
    f_x = solver.mkTerm(Kind.APPLY_UF, f, x)
    f_y = solver.mkTerm(Kind.APPLY_UF, f, y)
    summ = solver.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = solver.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = solver.mkTerm(Kind.APPLY_UF, p, f_y)
    # Assertions
    assertions =\
        solver.mkTerm(Kind.AND,\
                      solver.mkTerm(Kind.LEQ, zero, f_x),  # 0 <= f(x)
                       solver.mkTerm(Kind.LEQ, zero, f_y),  # 0 <= f(y)
                       solver.mkTerm(Kind.LEQ, summ, one),  # f(x) + f(y) <= 1
                       p_0.notTerm(),                        # not p(0)
                       p_f_y                                 # p(f(y))
                      )

    solver.checkSatAssuming(solver.mkTrue())
    solver.assertFormula(assertions)
    solver.checkSatAssuming(solver.mkTerm(Kind.DISTINCT, x, y))
    solver.checkSatAssuming(
        solver.mkFalse(),
         solver.mkTerm(Kind.DISTINCT, x, y))
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(n)
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(n, solver.mkTerm(Kind.DISTINCT, x, y))
    slv = cvc5.Solver()
    slv.checkSatAssuming(solver.mkTrue())


def test_set_logic(solver):
    solver.setLogic("AUFLIRA")
    with pytest.raises(RuntimeError):
        solver.setLogic("AF_BV")
    solver.assertFormula(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.setLogic("AUFLIRA")


def test_set_option(solver):
    solver.setOption("bv-sat-solver", "minisat")
    with pytest.raises(RuntimeError):
        solver.setOption("bv-sat-solver", "1")
    solver.assertFormula(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.setOption("bv-sat-solver", "minisat")


def test_reset_assertions(solver):
    solver.setOption("incremental", "true")

    bvSort = solver.mkBitVectorSort(4)
    one = solver.mkBitVector(4, 1)
    x = solver.mkConst(bvSort, "x")
    ule = solver.mkTerm(Kind.BITVECTOR_ULE, x, one)
    srem = solver.mkTerm(Kind.BITVECTOR_SREM, one, x)
    solver.push(4)
    slt = solver.mkTerm(Kind.BITVECTOR_SLT, srem, one)
    solver.resetAssertions()
    solver.checkSatAssuming(slt, ule)


def test_mk_sygus_grammar(solver):
    nullTerm = cvc5.Term(solver)
    boolTerm = solver.mkBoolean(True)
    boolVar = solver.mkVar(solver.getBooleanSort())
    intVar = solver.mkVar(solver.getIntegerSort())

    solver.mkGrammar([], [intVar])
    solver.mkGrammar([boolVar], [intVar])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([], [])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([], [nullTerm])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([], [boolTerm])
    with pytest.raises(RuntimeError):
        solver.mkGrammar([boolTerm], [intVar])
    slv = cvc5.Solver()
    boolVar2 = slv.mkVar(slv.getBooleanSort())
    intVar2 = slv.mkVar(slv.getIntegerSort())
    slv.mkGrammar([boolVar2], [intVar2])
    slv.mkGrammar([boolVar], [intVar2])
    slv.mkGrammar([boolVar2], [intVar])


def test_add_sygus_constraint(solver):
    solver.setOption("sygus", "true")
    nullTerm = cvc5.Term(solver)
    boolTerm = solver.mkBoolean(True)
    intTerm = solver.mkInteger(1)

    solver.addSygusConstraint(boolTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusConstraint(nullTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusConstraint(intTerm)

    slv = cvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.addSygusConstraint(boolTerm)


def test_get_sygus_constraints(solver):
    solver.setOption("sygus", "true")
    true_term = solver.mkBoolean(True)
    false_term = solver.mkBoolean(False)
    solver.addSygusConstraint(true_term)
    solver.addSygusConstraint(false_term)
    constraints = [true_term, false_term]
    assert solver.getSygusConstraints() == constraints


def test_add_sygus_assume(solver):
    solver.setOption("sygus", "true")
    nullTerm = cvc5.Term(solver)
    boolTerm = solver.mkBoolean(False)
    intTerm = solver.mkInteger(1)
    solver.addSygusAssume(boolTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusAssume(nullTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusAssume(intTerm)
    slv = cvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.addSygusAssume(boolTerm)


def test_get_sygus_assumptions(solver):
    solver.setOption("sygus", "true")
    true_term = solver.mkBoolean(True)
    false_term = solver.mkBoolean(False)
    solver.addSygusAssume(true_term)
    solver.addSygusAssume(false_term)
    assumptions = [true_term, false_term]
    assert solver.getSygusAssumptions() == assumptions


def test_add_sygus_inv_constraint(solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()
    real = solver.getRealSort()

    nullTerm = cvc5.Term(solver)
    intTerm = solver.mkInteger(1)

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
        solver.addSygusInvConstraint(nullTerm, pre, trans, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, nullTerm, trans, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, nullTerm, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans, nullTerm)

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
    slv = cvc5.Solver()
    slv.setOption("sygus", "true")
    boolean2 = slv.getBooleanSort()
    real2 = slv.getRealSort()
    inv22 = slv.declareFun("inv", [real2], boolean2)
    pre22 = slv.declareFun("pre", [real2], boolean2)
    trans22 = slv.declareFun("trans", [real2, real2], boolean2)
    post22 = slv.declareFun("post", [real2], boolean2)
    slv.addSygusInvConstraint(inv22, pre22, trans22, post22)
    slv.addSygusInvConstraint(inv, pre22, trans22, post22)
    slv.addSygusInvConstraint(inv22, pre, trans22, post22)
    slv.addSygusInvConstraint(inv22, pre22, trans, post22)
    slv.addSygusInvConstraint(inv22, pre22, trans22, post)


def test_check_synth(solver):
    with pytest.raises(RuntimeError):
        solver.checkSynth()
    solver.setOption("sygus", "true")
    solver.checkSynth()

def test_get_synth_solution(solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "false")

    nullTerm = cvc5.Term(solver)
    x = solver.mkBoolean(False)
    f = solver.synthFun("f", [], solver.getBooleanSort())

    with pytest.raises(RuntimeError):
        solver.getSynthSolution(f)

    res = solver.checkSynth()
    assert res.hasSolution()

    solver.getSynthSolution(f)
    solver.getSynthSolution(f)

    with pytest.raises(RuntimeError):
        solver.getSynthSolution(nullTerm)
    with pytest.raises(RuntimeError):
        solver.getSynthSolution(x)

    slv = cvc5.Solver()
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

def test_get_abduct(solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-abducts", "true")
    solver.setOption("incremental", "false")

    intSort = solver.getIntegerSort()
    zero = solver.mkInteger(0)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")

    solver.assertFormula(solver.mkTerm(Kind.GT, x, zero))
    conj = solver.mkTerm(Kind.GT, y, zero)
    output = solver.getAbduct(conj)
    assert not output.isNull() and output.getSort().isBoolean()

    boolean = solver.getBooleanSort()
    truen = solver.mkBoolean(True)
    start = solver.mkVar(boolean)
    output2 = cvc5.Term(solver)
    g = solver.mkGrammar([], [start])
    conj2 = solver.mkTerm(Kind.GT, x, zero)
    g.addRule(start, truen)
    output2 = solver.getAbduct(conj2, g)
    assert output2 == truen

def test_get_abduct2(solver):
    solver.setLogic("QF_LIA")
    solver.setOption("incremental", "false")
    intSort = solver.getIntegerSort()
    zero = solver.mkInteger(0)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    solver.assertFormula(solver.mkTerm(Kind.GT, x, zero))
    conj = solver.mkTerm(Kind.GT, y, zero)
    output = cvc5.Term(solver)
    with pytest.raises(RuntimeError):
        solver.getAbduct(conj)

def test_get_abduct_next(solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-abducts", "true")
    solver.setOption("incremental", "true")

    intSort = solver.getIntegerSort()
    zero = solver.mkInteger(0)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")

    solver.assertFormula(solver.mkTerm(Kind.GT, x, zero))
    conj = solver.mkTerm(Kind.GT, y, zero)
    output = solver.getAbduct(conj)
    output2 = solver.getAbductNext()
    assert output != output2


def test_get_interpolant(solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-interpolants", "true")
    solver.setOption("incremental", "false")

    intSort = solver.getIntegerSort()
    zero = solver.mkInteger(0)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    z = solver.mkConst(intSort, "z")

    solver.assertFormula(solver.mkTerm(
        Kind.GT, solver.mkTerm(Kind.ADD, x, y), zero))
    solver.assertFormula(solver.mkTerm(Kind.LT, x, zero))
    conj = solver.mkTerm(
            Kind.OR,
            solver.mkTerm(Kind.GT, solver.mkTerm(Kind.ADD, y, z), zero),
            solver.mkTerm(Kind.LT, z, zero))
    output = solver.getInterpolant(conj)
    assert output.getSort().isBoolean()

    boolean = solver.getBooleanSort()
    truen = solver.mkBoolean(True)
    start = solver.mkVar(boolean)
    g = solver.mkGrammar([], [start])
    conj2 = solver.mkTerm(Kind.EQUAL, zero, zero)
    g.addRule(start, truen)
    output2 = solver.getInterpolant(conj2, g)
    assert output2 == truen


def test_get_interpolant_next(solver):
    solver.setLogic("QF_LIA")
    solver.setOption("produce-interpolants", "true")
    solver.setOption("incremental", "true")

    intSort = solver.getIntegerSort()
    zero = solver.mkInteger(0)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    z = solver.mkConst(intSort, "z")

    solver.assertFormula(solver.mkTerm(
        Kind.GT, solver.mkTerm(Kind.ADD, x, y), zero))
    solver.assertFormula(solver.mkTerm(Kind.LT, x, zero))
    conj = solver.mkTerm(
            Kind.OR,
            solver.mkTerm(Kind.GT, solver.mkTerm(Kind.ADD, y, z), zero),
            solver.mkTerm(Kind.LT, z, zero))
    output = solver.getInterpolant(conj)
    output2 = solver.getInterpolantNext()

    assert output != output2


def test_declare_pool(solver):
    intSort = solver.getIntegerSort()
    setSort = solver.mkSetSort(intSort)
    zero = solver.mkInteger(0)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    # declare a pool with initial value  0, x, y
    p = solver.declarePool("p", intSort, [zero, x, y])
    # pool should have the same sort
    assert p.getSort() == setSort
    # cannot pass null sort
    nullSort = cvc5.Sort(solver)
    with pytest.raises(RuntimeError):
        solver.declarePool("i", nullSort, [])


def test_define_sort(solver):
    sortVar0 = solver.mkParamSort("T0")
    sortVar1 = solver.mkParamSort("T1")
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    arraySort0 = solver.mkArraySort(sortVar0, sortVar0)
    arraySort1 = solver.mkArraySort(sortVar0, sortVar1)
    # Now create instantiations of the defined sorts
    arraySort0.substitute(sortVar0, intSort)

    arraySort1.substitute([sortVar0, sortVar1], [intSort, realSort])


def test_get_model_domain_elements(solver):
    solver.setOption("produce-models", "true")
    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    z = solver.mkConst(uSort, "z")
    f = solver.mkTerm(Kind.DISTINCT, x, y, z)
    solver.assertFormula(f)
    solver.checkSat()
    solver.getModelDomainElements(uSort)
    assert len(solver.getModelDomainElements(uSort)) >= 3
    with pytest.raises(RuntimeError):
        solver.getModelDomainElements(intSort)

def test_get_model_domain_elements2(solver):
    solver.setOption("produce-models", "true")
    solver.setOption("finite-model-find", "true")
    uSort = solver.mkUninterpretedSort("u")
    x = solver.mkVar(uSort, "x")
    y = solver.mkVar(uSort, "y")
    eq = solver.mkTerm(Kind.EQUAL, x, y)
    bvl = solver.mkTerm(Kind.VARIABLE_LIST, x, y)
    f = solver.mkTerm(Kind.FORALL, bvl, eq)
    solver.assertFormula(f)
    solver.checkSat()
    solver.getModelDomainElements(uSort)
    assert len(solver.getModelDomainElements(uSort)) == 1


def test_get_synth_solutions(solver):
    solver.setOption("sygus", "true")
    solver.setOption("incremental", "false")

    nullTerm = cvc5.Term(solver)
    x = solver.mkBoolean(False)
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
        solver.getSynthSolutions([nullTerm])
    with pytest.raises(RuntimeError):
        solver.getSynthSolutions([x])

    slv = cvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.getSynthSolutions([x])


def test_get_value_sep_heap1(solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_get_value_sep_heap3(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap4(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_get_value_sep_nil1(solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_get_value_sep_nil3(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil4(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
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


def test_is_model_core_symbol(solver):
    solver.setOption("produce-models", "true")
    solver.setOption("model-cores", "simple")
    uSort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    z = solver.mkConst(uSort, "z")
    zero = solver.mkInteger(0)
    f = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, x, y))
    solver.assertFormula(f)
    solver.checkSat()
    assert solver.isModelCoreSymbol(x)
    assert solver.isModelCoreSymbol(y)
    assert not solver.isModelCoreSymbol(z)
    with pytest.raises(RuntimeError):
        solver.isModelCoreSymbol(zero)


def test_get_model(solver):
    solver.setOption("produce-models", "true")
    uSort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    z = solver.mkConst(uSort, "z")
    f = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, x, y))
    solver.assertFormula(f)
    solver.checkSat()
    sorts = [uSort]
    terms = [x, y]
    solver.getModel(sorts, terms)
    null = cvc5.Term(solver)
    terms.append(null)
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)


def test_get_model2(solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)


def test_get_model3(solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    solver.checkSat()
    solver.getModel(sorts, terms)
    integer = solver.getIntegerSort()
    sorts.append(integer)
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)


def test_issue5893(solver):
    slv = cvc5.Solver()
    bvsort4 = solver.mkBitVectorSort(4)
    bvsort8 = solver.mkBitVectorSort(8)
    arrsort = solver.mkArraySort(bvsort4, bvsort8)
    arr = solver.mkConst(arrsort, "arr")
    idx = solver.mkConst(bvsort4, "idx")
    ten = solver.mkBitVector(8, "10", 10)
    sel = solver.mkTerm(Kind.SELECT, arr, idx)
    distinct = solver.mkTerm(Kind.DISTINCT, sel, ten)
    distinct.getOp()


def test_issue7000(solver):
    s1 = solver.getIntegerSort()
    s2 = solver.mkFunctionSort(s1, s1)
    s3 = solver.getRealSort()
    t4 = solver.mkPi()
    t7 = solver.mkConst(s3, "_x5")
    t37 = solver.mkConst(s2, "_x32")
    t59 = solver.mkConst(s2, "_x51")
    t72 = solver.mkTerm(Kind.EQUAL, t37, t59)
    t74 = solver.mkTerm(Kind.GT, t4, t7)
    query = solver.mkTerm(Kind.AND, t72, t74, t72, t72)
    # throws logic exception since logic is not higher order by default
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(query.notTerm())


def test_mk_sygus_var(solver):
    solver.setOption("sygus", "true")
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)

    solver.declareSygusVar("", boolSort)
    solver.declareSygusVar("", funSort)
    solver.declareSygusVar("b", boolSort)
    with pytest.raises(RuntimeError):
        solver.declareSygusVar("", cvc5.Sort(solver))
    slv = cvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.declareSygusVar("", boolSort)


def test_synth_fun(solver):
    solver.setOption("sygus", "true")
    null = cvc5.Sort(solver)
    boolean = solver.getBooleanSort()
    integer = solver.getIntegerSort()

    nullTerm = cvc5.Term(solver)
    x = solver.mkVar(boolean)

    start1 = solver.mkVar(boolean)
    start2 = solver.mkVar(integer)

    g1 = solver.mkGrammar(x, [start1])
    g1.addRule(start1, solver.mkBoolean(False))

    g2 = solver.mkGrammar(x, [start2])
    g2.addRule(start2, solver.mkInteger(0))

    solver.synthFun("", [], boolean)
    solver.synthFun("f1", [x], boolean)
    solver.synthFun("f2", [x], boolean, g1)

    with pytest.raises(RuntimeError):
        solver.synthFun("f3", [nullTerm], boolean)
    with pytest.raises(RuntimeError):
        solver.synthFun("f4", [], null)
    with pytest.raises(RuntimeError):
        solver.synthFun("f6", [x], boolean, g2)
    slv = cvc5.Solver()
    slv.setOption("sygus", "true")
    x2 = slv.mkVar(slv.getBooleanSort())
    slv.synthFun("f1", [x2], slv.getBooleanSort())
    slv.synthFun("", [], solver.getBooleanSort())
    slv.synthFun("f1", [x], solver.getBooleanSort())


def test_tuple_project(solver):
    elements = [\
        solver.mkBoolean(True), \
        solver.mkInteger(3),\
        solver.mkString("C"),\
        solver.mkTerm(Kind.SET_SINGLETON, solver.mkString("Z"))]

    tuple = solver.mkTuple(elements)

    indices1 = []
    indices2 = [0]
    indices3 = [0, 1]
    indices4 = [0, 0, 2, 2, 3, 3, 0]
    indices5 = [4]
    indices6 = [0, 4]

    solver.mkTerm(solver.mkOp(Kind.TUPLE_PROJECT, *indices1), tuple)

    solver.mkTerm(solver.mkOp(Kind.TUPLE_PROJECT, *indices2), tuple)

    solver.mkTerm(solver.mkOp(Kind.TUPLE_PROJECT, *indices3), tuple)

    solver.mkTerm(solver.mkOp(Kind.TUPLE_PROJECT, *indices4), tuple)

    with pytest.raises(RuntimeError):
        solver.mkTerm(solver.mkOp(Kind.TUPLE_PROJECT, *indices5), tuple)
    with pytest.raises(RuntimeError):
        solver.mkTerm(solver.mkOp(Kind.TUPLE_PROJECT, *indices6), tuple)

    indices = [0, 3, 2, 0, 1, 2]

    op = solver.mkOp(Kind.TUPLE_PROJECT, *indices)
    projection = solver.mkTerm(op, tuple)

    datatype = tuple.getSort().getDatatype()
    constructor = datatype[0]

    for i in indices:

        selectorTerm = constructor[i].getTerm()
        selectedTerm = solver.mkTerm(Kind.APPLY_SELECTOR, selectorTerm, tuple)
        simplifiedTerm = solver.simplify(selectedTerm)
        assert elements[i] == simplifiedTerm

        assert "((_ tuple.project 0 3 2 0 1 2) (tuple true 3 \"C\" (set.singleton \"Z\")))" == str(
            projection)



def test_get_data_type_arity(solver):
  ctor1 = solver.mkDatatypeConstructorDecl("_x21")
  ctor2 = solver.mkDatatypeConstructorDecl("_x31")
  s3 = solver.declareDatatype("_x17", ctor1, ctor2)
  assert s3.getDatatypeArity() == 0


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

def test_get_difficulty3(solver):
  solver.setOption("produce-difficulty", "true")
  intSort = solver.getIntegerSort()
  x = solver.mkConst(intSort, "x")
  zero = solver.mkInteger(0)
  ten = solver.mkInteger(10)
  f0 = solver.mkTerm(Kind.GEQ, x, ten)
  f1 = solver.mkTerm(Kind.GEQ, zero, x)
  solver.checkSat()
  dmap = solver.getDifficulty()
  # difficulty should map assertions to integer values
  for key, value in dmap.items():
    assert key == f0 or key == f1
    assert value.getKind() == Kind.CONST_INTEGER

def test_get_model(solver):
    solver.setOption("produce-models", "true")
    uSort = solver.mkUninterpretedSort("u")
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    z = solver.mkConst(uSort, "z")
    f = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, x, y));
    solver.assertFormula(f)
    solver.checkSat()
    sorts = [uSort]
    terms = [x, y]
    solver.getModel(sorts, terms)
    null = cvc5.Term(solver)
    terms += [null]
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)

def test_get_model2(solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)

def test_get_model_3(solver):
    solver.setOption("produce-models", "true")
    sorts = []
    terms = []
    solver.checkSat()
    solver.getModel(sorts, terms)
    integer = solver.getIntegerSort()
    sorts += [integer]
    with pytest.raises(RuntimeError):
        solver.getModel(sorts, terms)

def test_get_option_names(solver):
    names = solver.getOptionNames()
    assert len(names) > 100
    assert "verbose" in names
    assert "foobar" not in names

def test_get_quantifier_elimination(solver):
    x = solver.mkVar(solver.getBooleanSort(), "x")
    forall = solver.mkTerm(
            Kind.FORALL,
            solver.mkTerm(Kind.VARIABLE_LIST, x),
            solver.mkTerm(Kind.OR, x, solver.mkTerm(Kind.NOT, x)))
    with pytest.raises(RuntimeError):
        solver.getQuantifierElimination(cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.getQuantifierElimination(cvc5.Solver().mkBoolean(False))
    solver.getQuantifierElimination(forall)

def test_get_quantifier_elimination_disjunct(solver):
    x = solver.mkVar(solver.getBooleanSort(), "x")
    forall = solver.mkTerm(
            Kind.FORALL,
            solver.mkTerm(Kind.VARIABLE_LIST, x),
            solver.mkTerm(Kind.OR, x, solver.mkTerm(Kind.NOT, x)))
    with pytest.raises(RuntimeError):
        solver.getQuantifierEliminationDisjunct(cvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.getQuantifierEliminationDisjunct(cvc5.Solver().mkBoolean(False))
    solver.getQuantifierEliminationDisjunct(forall)

def test_get_version(solver):
    print(solver.getVersion())
