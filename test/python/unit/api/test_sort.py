###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Makai Mann
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for sort API.
#
# Obtained by translating test/unit/api/sort_black.cpp
##

import pytest
import pycvc5
from pycvc5 import kinds
from pycvc5 import Sort


@pytest.fixture
def solver():
    return pycvc5.Solver()


def create_datatype_sort(solver):
    intSort = solver.getIntegerSort()
    # create datatype sort to test
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    return dtypeSort


def create_param_datatype_sort(solver):
    sort = solver.mkParamSort("T")
    paramDtypeSpec = solver.mkDatatypeDecl("paramlist", sort)
    paramCons = solver.mkDatatypeConstructorDecl("cons")
    paramNil = solver.mkDatatypeConstructorDecl("nil")
    paramCons.addSelector("head", sort)
    paramDtypeSpec.addConstructor(paramCons)
    paramDtypeSpec.addConstructor(paramNil)
    paramDtypeSort = solver.mkDatatypeSort(paramDtypeSpec)
    return paramDtypeSort


def test_operators_comparison(solver):
    solver.getIntegerSort() == Sort(solver)
    solver.getIntegerSort() != Sort(solver)
    solver.getIntegerSort() < Sort(solver)
    solver.getIntegerSort() <= Sort(solver)
    solver.getIntegerSort() > Sort(solver)
    solver.getIntegerSort() >= Sort(solver)


def test_is_boolean(solver):
    assert solver.getBooleanSort().isBoolean()
    Sort(solver).isBoolean()


def test_is_integer(solver):
    assert solver.getIntegerSort().isInteger()
    assert not solver.getRealSort().isInteger()
    Sort(solver).isInteger()


def test_is_real(solver):
    assert solver.getRealSort().isReal()
    assert not solver.getIntegerSort().isReal()
    Sort(solver).isReal()


def test_is_string(solver):
    assert solver.getStringSort().isString()
    Sort(solver).isString()


def test_is_reg_exp(solver):
    assert solver.getRegExpSort().isRegExp()
    Sort(solver).isRegExp()


def test_is_rounding_mode(solver):
    if solver.supportsFloatingPoint():
        assert solver.getRoundingModeSort().isRoundingMode()
        Sort(solver).isRoundingMode()


def test_is_bit_vector(solver):
    assert solver.mkBitVectorSort(8).isBitVector()
    Sort(solver).isBitVector()


def test_is_floating_point(solver):
    if solver.supportsFloatingPoint():
        assert solver.mkFloatingPointSort(8, 24).isFloatingPoint()
        Sort(solver).isFloatingPoint()


def test_is_datatype(solver):
    dt_sort = create_datatype_sort(solver)
    assert dt_sort.isDatatype()
    Sort(solver).isDatatype()


def test_is_parametric_datatype(solver):
    param_dt_sort = create_param_datatype_sort(solver)
    assert param_dt_sort.isParametricDatatype()
    Sort(solver).isParametricDatatype()


def test_is_constructor(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getConstructorTerm().getSort()
    assert cons_sort.isConstructor()
    Sort(solver).isConstructor()


def test_is_selector(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    dt0 = dt[0]
    dt01 = dt0[1]
    cons_sort = dt01.getSelectorTerm().getSort()
    assert cons_sort.isSelector()
    Sort(solver).isSelector()


def test_is_tester(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getTesterTerm().getSort()
    assert cons_sort.isTester()
    Sort(solver).isTester()


def test_is_function(solver):
    fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                     solver.getIntegerSort())
    assert fun_sort.isFunction()
    Sort(solver).isFunction()


def test_is_predicate(solver):
    pred_sort = solver.mkPredicateSort(solver.getRealSort())
    assert pred_sort.isPredicate()
    Sort(solver).isPredicate()


def test_is_tuple(solver):
    tup_sort = solver.mkTupleSort(solver.getRealSort())
    assert tup_sort.isTuple()
    Sort(solver).isTuple()


def test_is_record(solver):
    rec_sort = solver.mkRecordSort([("asdf", solver.getRealSort())])
    assert rec_sort.isRecord()
    Sort(solver).isRecord()


def test_is_array(solver):
    arr_sort = solver.mkArraySort(solver.getRealSort(),
                                  solver.getIntegerSort())
    assert arr_sort.isArray()
    Sort(solver).isArray()


def test_is_set(solver):
    set_sort = solver.mkSetSort(solver.getRealSort())
    assert set_sort.isSet()
    Sort(solver).isSet()


def test_is_bag(solver):
    bag_sort = solver.mkBagSort(solver.getRealSort())
    assert bag_sort.isBag()
    Sort(solver).isBag()


def test_is_sequence(solver):
    seq_sort = solver.mkSequenceSort(solver.getRealSort())
    assert seq_sort.isSequence()
    Sort(solver).isSequence()


def test_is_uninterpreted(solver):
    un_sort = solver.mkUninterpretedSort("asdf")
    assert un_sort.isUninterpretedSort()
    Sort(solver).isUninterpretedSort()


def test_is_sort_constructor(solver):
    sc_sort = solver.mkSortConstructorSort("asdf", 1)
    assert sc_sort.isSortConstructor()
    Sort(solver).isSortConstructor()


def test_is_first_class(solver):
    fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                     solver.getIntegerSort())
    assert solver.getIntegerSort().isFirstClass()
    assert fun_sort.isFirstClass()
    reSort = solver.getRegExpSort()
    assert not reSort.isFirstClass()
    Sort(solver).isFirstClass()


def test_is_function_like(solver):
    fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                     solver.getIntegerSort())
    assert not solver.getIntegerSort().isFunctionLike()
    assert fun_sort.isFunctionLike()

    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0][1].getSelectorTerm().getSort()
    assert cons_sort.isFunctionLike()

    Sort(solver).isFunctionLike()


def test_is_subsort_of(solver):
    assert solver.getIntegerSort().isSubsortOf(solver.getIntegerSort())
    assert solver.getIntegerSort().isSubsortOf(solver.getRealSort())
    assert not solver.getIntegerSort().isSubsortOf(solver.getBooleanSort())
    Sort(solver).isSubsortOf(Sort(solver))


def test_is_comparable_to(solver):
    assert solver.getIntegerSort().isComparableTo(solver.getIntegerSort())
    assert solver.getIntegerSort().isComparableTo(solver.getRealSort())
    assert not solver.getIntegerSort().isComparableTo(solver.getBooleanSort())
    Sort(solver).isComparableTo(Sort(solver))


def test_get_datatype(solver):
    dtypeSort = create_datatype_sort(solver)
    dtypeSort.getDatatype()
    # create bv sort, check should fail
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getDatatype()


def test_datatype_sorts(solver):
    intSort = solver.getIntegerSort()
    dtypeSort = create_datatype_sort(solver)
    dt = dtypeSort.getDatatype()
    assert not dtypeSort.isConstructor()
    with pytest.raises(RuntimeError):
        dtypeSort.getConstructorCodomainSort()
    with pytest.raises(RuntimeError):
        dtypeSort.getConstructorDomainSorts()
    with pytest.raises(RuntimeError):
        dtypeSort.getConstructorArity()

    # get constructor
    dcons = dt[0]
    consTerm = dcons.getConstructorTerm()
    consSort = consTerm.getSort()
    assert consSort.isConstructor()
    assert not consSort.isTester()
    assert not consSort.isSelector()
    assert consSort.getConstructorArity() == 2
    consDomSorts = consSort.getConstructorDomainSorts()
    assert consDomSorts[0] == intSort
    assert consDomSorts[1] == dtypeSort
    assert consSort.getConstructorCodomainSort() == dtypeSort

    # get tester
    isConsTerm = dcons.getTesterTerm()
    assert isConsTerm.getSort().isTester()
    booleanSort = solver.getBooleanSort()

    assert isConsTerm.getSort().getTesterDomainSort() == dtypeSort
    assert isConsTerm.getSort().getTesterCodomainSort() == booleanSort
    with pytest.raises(RuntimeError):
        booleanSort.getTesterDomainSort()
    with pytest.raises(RuntimeError):
        booleanSort.getTesterCodomainSort()

    # get selector
    dselTail = dcons[1]
    tailTerm = dselTail.getSelectorTerm()
    assert tailTerm.getSort().isSelector()
    assert tailTerm.getSort().getSelectorDomainSort() == dtypeSort
    assert tailTerm.getSort().getSelectorCodomainSort() == dtypeSort
    with pytest.raises(RuntimeError):
        booleanSort.getSelectorDomainSort()
    with pytest.raises(RuntimeError):
        booleanSort.getSelectorCodomainSort()


def test_instantiate(solver):
    # instantiate parametric datatype, check should not fail
    paramDtypeSort = create_param_datatype_sort(solver)
    paramDtypeSort.instantiate([solver.getIntegerSort()])
    # instantiate non-parametric datatype sort, check should fail
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    with pytest.raises(RuntimeError):
        dtypeSort.instantiate([solver.getIntegerSort()])


def test_get_function_arity(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    funSort.getFunctionArity()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionArity()


def test_get_function_domain_sorts(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    funSort.getFunctionDomainSorts()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionDomainSorts()


def test_get_function_codomain_sort(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    funSort.getFunctionCodomainSort()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionCodomainSort()


def test_get_array_index_sort(solver):
    elementSort = solver.mkBitVectorSort(32)
    indexSort = solver.mkBitVectorSort(32)
    arraySort = solver.mkArraySort(indexSort, elementSort)
    arraySort.getArrayIndexSort()
    with pytest.raises(RuntimeError):
        indexSort.getArrayIndexSort()


def test_get_array_element_sort(solver):
    elementSort = solver.mkBitVectorSort(32)
    indexSort = solver.mkBitVectorSort(32)
    arraySort = solver.mkArraySort(indexSort, elementSort)
    arraySort.getArrayElementSort()
    with pytest.raises(RuntimeError):
        indexSort.getArrayElementSort()


def test_get_set_element_sort(solver):
    setSort = solver.mkSetSort(solver.getIntegerSort())
    setSort.getSetElementSort()
    elementSort = setSort.getSetElementSort()
    assert elementSort == solver.getIntegerSort()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSetElementSort()


def test_get_bag_element_sort(solver):
    bagSort = solver.mkBagSort(solver.getIntegerSort())
    bagSort.getBagElementSort()
    elementSort = bagSort.getBagElementSort()
    assert elementSort == solver.getIntegerSort()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getBagElementSort()


def test_get_sequence_element_sort(solver):
    seqSort = solver.mkSequenceSort(solver.getIntegerSort())
    assert seqSort.isSequence()
    seqSort.getSequenceElementSort()
    bvSort = solver.mkBitVectorSort(32)
    assert not bvSort.isSequence()
    with pytest.raises(RuntimeError):
        bvSort.getSequenceElementSort()


def test_get_uninterpreted_sort_name(solver):
    uSort = solver.mkUninterpretedSort("u")
    uSort.getUninterpretedSortName()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getUninterpretedSortName()


def test_is_uninterpreted_sort_parameterized(solver):
    uSort = solver.mkUninterpretedSort("u")
    assert not uSort.isUninterpretedSortParameterized()
    sSort = solver.mkSortConstructorSort("s", 1)
    siSort = sSort.instantiate([uSort])
    assert siSort.isUninterpretedSortParameterized()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.isUninterpretedSortParameterized()


def test_get_uninterpreted_sort_paramsorts(solver):
    uSort = solver.mkUninterpretedSort("u")
    uSort.getUninterpretedSortParamSorts()
    sSort = solver.mkSortConstructorSort("s", 2)
    siSort = sSort.instantiate([uSort, uSort])
    assert len(siSort.getUninterpretedSortParamSorts()) == 2
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getUninterpretedSortParamSorts()


def test_get_uninterpreted_sort_constructor_name(solver):
    sSort = solver.mkSortConstructorSort("s", 2)
    sSort.getSortConstructorName()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSortConstructorName()


def test_get_uninterpreted_sort_constructor_arity(solver):
    sSort = solver.mkSortConstructorSort("s", 2)
    sSort.getSortConstructorArity()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSortConstructorArity()


def test_get_bv_size(solver):
    bvSort = solver.mkBitVectorSort(32)
    bvSort.getBVSize()
    setSort = solver.mkSetSort(solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getBVSize()


def test_get_fp_exponent_size(solver):
    if solver.supportsFloatingPoint():
        fpSort = solver.mkFloatingPointSort(4, 8)
        fpSort.getFPExponentSize()
        setSort = solver.mkSetSort(solver.getIntegerSort())
        with pytest.raises(RuntimeError):
            setSort.getFPExponentSize()


def test_get_fp_significand_size(solver):
    if solver.supportsFloatingPoint():
        fpSort = solver.mkFloatingPointSort(4, 8)
        fpSort.getFPSignificandSize()
        setSort = solver.mkSetSort(solver.getIntegerSort())
        with pytest.raises(RuntimeError):
            setSort.getFPSignificandSize()


def test_get_datatype_paramsorts(solver):
    # create parametric datatype, check should not fail
    sort = solver.mkParamSort("T")
    paramDtypeSpec = solver.mkDatatypeDecl("paramlist", sort)
    paramCons = solver.mkDatatypeConstructorDecl("cons")
    paramNil = solver.mkDatatypeConstructorDecl("nil")
    paramCons.addSelector("head", sort)
    paramDtypeSpec.addConstructor(paramCons)
    paramDtypeSpec.addConstructor(paramNil)
    paramDtypeSort = solver.mkDatatypeSort(paramDtypeSpec)
    paramDtypeSort.getDatatypeParamSorts()
    # create non-parametric datatype sort, check should fail
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    with pytest.raises(RuntimeError):
        dtypeSort.getDatatypeParamSorts()


def test_get_datatype_arity(solver):
    # create datatype sort, check should not fail
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    dtypeSort.getDatatypeArity()
    # create bv sort, check should fail
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getDatatypeArity()


def test_get_tuple_length(solver):
    tupleSort = solver.mkTupleSort(
        [solver.getIntegerSort(),
         solver.getIntegerSort()])
    tupleSort.getTupleLength()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleLength()


def test_get_tuple_sorts(solver):
    tupleSort = solver.mkTupleSort(
        [solver.getIntegerSort(),
         solver.getIntegerSort()])
    tupleSort.getTupleSorts()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleSorts()


def test_sort_compare(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    bvSort = solver.mkBitVectorSort(32)
    bvSort2 = solver.mkBitVectorSort(32)
    assert bvSort >= bvSort2
    assert bvSort <= bvSort2
    assert (intSort > boolSort) != (intSort < boolSort)
    assert (intSort > bvSort or intSort == bvSort) == (intSort >= bvSort)


def test_sort_subtyping(solver):
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    assert intSort.isSubsortOf(realSort)
    assert not realSort.isSubsortOf(intSort)
    assert intSort.isComparableTo(realSort)
    assert realSort.isComparableTo(intSort)

    arraySortII = solver.mkArraySort(intSort, intSort)
    arraySortIR = solver.mkArraySort(intSort, realSort)
    assert not arraySortII.isComparableTo(intSort)
    # we do not support subtyping for arrays
    assert not arraySortII.isComparableTo(arraySortIR)

    setSortI = solver.mkSetSort(intSort)
    setSortR = solver.mkSetSort(realSort)
    # we don't support subtyping for sets
    assert not setSortI.isComparableTo(setSortR)
    assert not setSortI.isSubsortOf(setSortR)
    assert not setSortR.isComparableTo(setSortI)
    assert not setSortR.isSubsortOf(setSortI)


def test_sort_scoped_tostring(solver):
    name = "uninterp-sort"
    bvsort8 = solver.mkBitVectorSort(8)
    uninterp_sort = solver.mkUninterpretedSort(name)
    assert str(bvsort8) == "(_ BitVec 8)"
    assert str(uninterp_sort) == name
    solver2 = pycvc5.Solver()
    assert str(bvsort8) == "(_ BitVec 8)"
    assert str(uninterp_sort) == name
