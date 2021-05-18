###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Ying Sheng
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import pycvc5
import sys

from pycvc5 import kinds


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_recoverable_exception(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    with pytest.raises(RuntimeError):
        c = solver.getValue(x)


def test_supports_floating_point(solver):
    if solver.supportsFloatingPoint():
        solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)
    else:
        with pytest.raises(RuntimeError):
            solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)


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
    if solver.supportsFloatingPoint():
        solver.getRoundingModeSort()
    else:
        with pytest.raises(RuntimeError):
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

    if (solver.supportsFloatingPoint()):
        fpSort = solver.mkFloatingPointSort(3, 5)
        solver.mkArraySort(fpSort, fpSort)
        solver.mkArraySort(bvSort, fpSort)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkArraySort(boolSort, boolSort)


def test_mk_bit_vector_sort(solver):
    solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        solver.mkBitVectorSort(0)


def test_mk_floating_point_sort(solver):
    if solver.supportsFloatingPoint():
        solver.mkFloatingPointSort(4, 8)
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(0, 8)
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(4, 0)
    else:
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(4, 8)


def test_mk_datatype_sort(solver):
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    solver.mkDatatypeSort(dtypeSpec)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSort(dtypeSpec)

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSort(throwsDtypeSpec)


def test_mk_datatype_sorts(solver):
    slv = pycvc5.Solver()

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
    solver.mkDatatypeSorts(decls, [])

    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(decls, [])

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    throwsDecls = [throwsDtypeSpec]
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(throwsDecls, [])

    # with unresolved sorts
    unresList = solver.mkUninterpretedSort("ulist")
    unresSorts = [unresList]
    ulist = solver.mkDatatypeDecl("ulist")
    ucons = solver.mkDatatypeConstructorDecl("ucons")
    ucons.addSelector("car", unresList)
    ucons.addSelector("cdr", unresList)
    ulist.addConstructor(ucons)
    unil = solver.mkDatatypeConstructorDecl("unil")
    ulist.addConstructor(unil)
    udecls = [ulist]

    solver.mkDatatypeSorts(udecls, unresSorts)
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(udecls, unresSorts)


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

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(slv.mkUninterpretedSort("u"),\
                solver.getIntegerSort())
    sorts1 = [solver.getBooleanSort(),\
            slv.getIntegerSort(),\
            solver.getIntegerSort()]
    sorts2 = [slv.getBooleanSort(), slv.getIntegerSort()]
    slv.mkFunctionSort(sorts2, slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(sorts1, slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(sorts2, solver.getIntegerSort())


def test_mk_param_sort(solver):
    solver.mkParamSort("T")
    solver.mkParamSort("")


def test_mk_predicate_sort(solver):
    solver.mkPredicateSort([solver.getIntegerSort()])
    with pytest.raises(RuntimeError):
        solver.mkPredicateSort([])

    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    # functions as arguments are allowed
    solver.mkPredicateSort([solver.getIntegerSort(), funSort])

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkPredicateSort([solver.getIntegerSort()])


def test_mk_record_sort(solver):
    fields = [("b", solver.getBooleanSort()),\
              ("bv", solver.mkBitVectorSort(8)),\
              ("i", solver.getIntegerSort())]
    empty = []
    solver.mkRecordSort(fields)
    solver.mkRecordSort(empty)
    recSort = solver.mkRecordSort(fields)
    recSort.getDatatype()


def test_mk_set_sort(solver):
    solver.mkSetSort(solver.getBooleanSort())
    solver.mkSetSort(solver.getIntegerSort())
    solver.mkSetSort(solver.mkBitVectorSort(4))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSetSort(solver.mkBitVectorSort(4))


def test_mk_sequence_sort(solver):
    solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkSequenceSort(\
            solver.mkSequenceSort(solver.getIntegerSort()))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSequenceSort(solver.getIntegerSort())


def test_mk_uninterpreted_sort(solver):
    solver.mkUninterpretedSort("u")
    solver.mkUninterpretedSort("")


def test_mk_sortConstructor_sort(solver):
    solver.mkSortConstructorSort("s", 2)
    solver.mkSortConstructorSort("", 2)
    with pytest.raises(RuntimeError):
        solver.mkSortConstructorSort("", 0)


def test_mk_tuple_sort(solver):
    solver.mkTupleSort([solver.getIntegerSort()])
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkTupleSort([solver.getIntegerSort(), funSort])

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkTupleSort([solver.getIntegerSort()])


def test_mk_var(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkVar(boolSort)
    solver.mkVar(funSort)
    solver.mkVar(boolSort, "b")
    solver.mkVar(funSort, "")
    with pytest.raises(RuntimeError):
        solver.mkVar(pycvc5.Sort(solver))
    with pytest.raises(RuntimeError):
        solver.mkVar(pycvc5.Sort(solver), "a")
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkVar(boolSort, "x")


def test_mk_boolean(solver):
    solver.mkBoolean(True)
    solver.mkBoolean(False)


def test_mk_rounding_mode(solver):
    if solver.supportsFloatingPoint():
        solver.mkRoundingMode(pycvc5.RoundTowardZero)
    else:
        with pytest.raises(RuntimeError):
            solver.mkRoundingMode(pycvc5.RoundTowardZero)


def test_mk_uninterpreted_const(solver):
    solver.mkUninterpretedConst(solver.getBooleanSort(), 1)
    with pytest.raises(RuntimeError):
        solver.mkUninterpretedConst(pycvc5.Sort(solver), 1)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkUninterpretedConst(solver.getBooleanSort(), 1)


def test_mk_floating_point(solver):
    t1 = solver.mkBitVector(8)
    t2 = solver.mkBitVector(4)
    t3 = solver.mkInteger(2)
    if (solver.supportsFloatingPoint()):
        solver.mkFloatingPoint(3, 5, t1)
    else:
        with pytest.raises(RuntimeError):
            solver.mkFloatingPoint(3, 5, t1)

    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(0, 5, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(0, 5, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 0, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)

    if (solver.supportsFloatingPoint()):
        slv = pycvc5.Solver()
        with pytest.raises(RuntimeError):
            slv.mkFloatingPoint(3, 5, t1)


def test_mk_empty_set(solver):
    slv = pycvc5.Solver()
    s = solver.mkSetSort(solver.getBooleanSort())
    solver.mkEmptySet(pycvc5.Sort(solver))
    solver.mkEmptySet(s)
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptySet(s)


def test_mk_empty_sequence(solver):
    slv = pycvc5.Solver()
    s = solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkEmptySequence(s)
    solver.mkEmptySequence(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptySequence(s)


def test_mk_false(solver):
    solver.mkFalse()
    solver.mkFalse()


def test_mk_nan(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkNaN(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkNaN(3, 5)


def test_mk_neg_zero(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkNegZero(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkNegZero(3, 5)


def test_mk_neg_inf(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkNegInf(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkNegInf(3, 5)


def test_mk_pos_inf(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkPosInf(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkPosInf(3, 5)


def test_mk_pos_zero(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkPosZero(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkPosZero(3, 5)


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


def test_mk_regexp_empty(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(kinds.StringInRegexp, s, solver.mkRegexpEmpty())


def test_mk_regexp_sigma(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(kinds.StringInRegexp, s, solver.mkRegexpSigma())


def test_mk_sep_nil(solver):
    solver.mkSepNil(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkSepNil(pycvc5.Sort(solver))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSepNil(solver.getIntegerSort())


def test_mk_true(solver):
    solver.mkTrue()
    solver.mkTrue()


def test_mk_universe_set(solver):
    solver.mkUniverseSet(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkUniverseSet(pycvc5.Sort(solver))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
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
        solver.mkConst(pycvc5.Sort(solver))
    with pytest.raises(RuntimeError):
        solver.mkConst(pycvc5.Sort(solver), "a")

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkConst(boolSort)


def test_mk_const_array(solver):
    intSort = solver.getIntegerSort()
    arrSort = solver.mkArraySort(intSort, intSort)
    zero = solver.mkInteger(0)
    constArr = solver.mkConstArray(arrSort, zero)

    solver.mkConstArray(arrSort, zero)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(pycvc5.Sort(solver), zero)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, solver.mkBitVector(1, 1))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(intSort, zero)
    slv = pycvc5.Solver()
    zero2 = slv.mkInteger(0)
    arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkConstArray(arrSort2, zero)
    with pytest.raises(RuntimeError):
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
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.declareFun("f1", [], bvSort)


def test_declare_sort(solver):
    solver.declareSort("s", 0)
    solver.declareSort("s", 2)
    solver.declareSort("", 2)


def test_define_fun(solver):
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
    solver.defineFun("f", [], bvSort, v1)
    solver.defineFun("ff", [b1, b2], bvSort, v1)
    solver.defineFun(f1, [b1, b11], v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("ff", [v1, b2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("fff", [b1], bvSort, v3)
    with pytest.raises(RuntimeError):
        solver.defineFun("ffff", [b1], funSort2, v3)
    # b3 has function sort, which is allowed as an argument
    solver.defineFun("fffff", [b1, b3], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [v1, b11], v1)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [b1], v1)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [b1, b11], v2)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [b1, b11], v3)
    with pytest.raises(RuntimeError):
        solver.defineFun(f2, [b1], v2)
    with pytest.raises(RuntimeError):
        solver.defineFun(f3, [b1], v1)

    slv = pycvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    with pytest.raises(RuntimeError):
        slv.defineFun("f", [], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("f", [], bvSort2, v1)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b1, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b2], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b22], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b22], bvSort2, v1)


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

    slv = pycvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    slv.defineFunRec("f", [], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("f", [], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("f", [], bvSort2, v1)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b1, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b12, b2], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b12, b22], bvSort, v12)
    with pytest.raises(RuntimeError):
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


def test_uf_iteration(solver):
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort([intSort, intSort], intSort)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    f = solver.mkConst(funSort, "f")
    fxy = solver.mkTerm(kinds.ApplyUf, f, x, y)

    # Expecting the uninterpreted function to be one of the children
    expected_children = [f, x, y]
    idx = 0
    for c in fxy:
        assert idx < 3
        assert c == expected_children[idx]
        idx = idx + 1


def test_get_info(solver):
    solver.getInfo("name")
    with pytest.raises(RuntimeError):
        solver.getInfo("asdf")


def test_get_op(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    ext = solver.mkOp(kinds.BVExtract, 2, 1)
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

    consTerm = consList.getConstructorTerm("cons")
    nilTerm = consList.getConstructorTerm("nil")
    headTerm = consList["cons"].getSelectorTerm("head")

    listnil = solver.mkTerm(kinds.ApplyConstructor, nilTerm)
    listcons1 = solver.mkTerm(kinds.ApplyConstructor, consTerm,
                              solver.mkInteger(1), listnil)
    listhead = solver.mkTerm(kinds.ApplySelector, headTerm, listcons1)

    assert listnil.hasOp()
    assert listcons1.hasOp()
    assert listhead.hasOp()


def test_get_option(solver):
    solver.getOption("incremental")
    with pytest.raises(RuntimeError):
        solver.getOption("asdf")


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
