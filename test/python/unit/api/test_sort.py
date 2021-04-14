#####################
## test_sort.py
## Top contributors (to current version):
##   Makai Mann, Andres Noetzli, Mudathir Mohamed
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
import pytest
import pycvc4
from pycvc4 import kinds
from pycvc4 import Sort


@pytest.fixture
def solver():
    return pycvc4.Solver()


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
    try:
        solver.getIntegerSort() == Sort(solver)
        solver.getIntegerSort() != Sort(solver)
        solver.getIntegerSort() < Sort(solver)
        solver.getIntegerSort() <= Sort(solver)
        solver.getIntegerSort() > Sort(solver)
        solver.getIntegerSort() >= Sort(solver)
    except RuntimeError:
        pytest.fail()


def test_is_boolean(solver):
    assert (solver.getBooleanSort().isBoolean())
    try:
        Sort(solver).isBoolean()
    except RuntimeError:
        pytest.fail()


def test_is_integer(solver):
    assert (solver.getIntegerSort().isInteger())
    assert (not solver.getRealSort().isInteger())
    try:
        Sort(solver).isInteger()
    except RuntimeError:
        pytest.fail()


def test_is_real(solver):
    assert (solver.getRealSort().isReal())
    assert (not solver.getIntegerSort().isReal())
    try:
        Sort(solver).isReal()
    except RuntimeError:
        pytest.fail()


def test_is_string(solver):
    assert (solver.getStringSort().isString())
    try:
        Sort(solver).isString()
    except RuntimeError:
        pytest.fail()


def test_is_reg_exp(solver):
    assert (solver.getRegExpSort().isRegExp())
    try:
        Sort(solver).isRegExp()
    except RuntimeError:
        pytest.fail()


def test_is_rounding_mode(solver):
    if solver.supportsFloatingPoint():
        assert (solver.getRoundingModeSort().isRoundingMode())
        try:
            Sort(solver).isRoundingMode()
        except RuntimeError:
            pytest.fail()


def test_is_bit_vector(solver):
    assert (solver.mkBitVectorSort(8).isBitVector())
    try:
        Sort(solver).isBitVector()
    except RuntimeError:
        pytest.fail()


def test_is_floating_point(solver):
    if solver.supportsFloatingPoint():
        assert (solver.mkFloatingPointSort(8, 24).isFloatingPoint())
        try:
            Sort(solver).isFloatingPoint()
        except RuntimeError:
            pytest.fail()


def test_is_datatype(solver):
    dt_sort = create_datatype_sort(solver)
    assert (dt_sort.isDatatype())
    try:
        Sort(solver).isDatatype()
    except RuntimeError:
        pytest.fail()


def test_is_parametric_datatype(solver):
    param_dt_sort = create_param_datatype_sort(solver)
    assert (param_dt_sort.isParametricDatatype())
    try:
        Sort(solver).isParametricDatatype()
    except RuntimeError:
        pytest.fail()


def test_is_constructor(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getConstructorTerm().getSort()
    assert (cons_sort.isConstructor())
    try:
        Sort(solver).isConstructor()
    except RuntimeError:
        pytest.fail()


def test_is_selector(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    dt0 = dt[0]
    dt01 = dt0[1]
    cons_sort = dt01.getSelectorTerm().getSort()
    assert (cons_sort.isSelector())
    try:
        Sort(solver).isSelector()
    except RuntimeError:
        pytest.fail()


def test_is_tester(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getTesterTerm().getSort()
    assert (cons_sort.isTester())
    try:
        Sort(solver).isTester()
    except RuntimeError:
        pytest.fail()


def test_is_function(solver):
    fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                     solver.getIntegerSort())
    assert (fun_sort.isFunction())
    try:
        Sort(solver).isFunction()
    except RuntimeError:
        pytest.fail()


def test_is_predicate(solver):
    pred_sort = solver.mkPredicateSort(solver.getRealSort())
    assert (pred_sort.isPredicate())
    try:
        Sort(solver).isPredicate()
    except RuntimeError:
        pytest.fail()


def test_is_tuple(solver):
    tup_sort = solver.mkTupleSort(solver.getRealSort())
    assert (tup_sort.isTuple())
    try:
        Sort(solver).isTuple()
    except RuntimeError:
        pytest.fail()


def test_is_record(solver):
    rec_sort = solver.mkRecordSort([("asdf", solver.getRealSort())])
    assert (rec_sort.isRecord())
    try:
        Sort(solver).isRecord()
    except RuntimeError:
        pytest.fail()


def test_is_array(solver):
    arr_sort = solver.mkArraySort(solver.getRealSort(),
                                  solver.getIntegerSort())
    assert (arr_sort.isArray())
    try:
        Sort(solver).isArray()
    except RuntimeError:
        pytest.fail()


def test_is_set(solver):
    set_sort = solver.mkSetSort(solver.getRealSort())
    assert (set_sort.isSet())
    try:
        Sort(solver).isSet()
    except RuntimeError:
        pytest.fail()


def test_is_bag(solver):
    bag_sort = solver.mkBagSort(solver.getRealSort())
    assert (bag_sort.isBag())
    try:
        Sort(solver).isBag()
    except RuntimeError:
        pytest.fail()


def test_is_sequence(solver):
    seq_sort = solver.mkSequenceSort(solver.getRealSort())
    assert (seq_sort.isSequence())
    try:
        Sort(solver).isSequence()
    except RuntimeError:
        pytest.fail()


def test_is_uninterpreted(solver):
    un_sort = solver.mkUninterpretedSort("asdf")
    assert (un_sort.isUninterpretedSort())
    try:
        Sort(solver).isUninterpretedSort()
    except RuntimeError:
        pytest.fail()


def test_is_sort_constructor(solver):
    sc_sort = solver.mkSortConstructorSort("asdf", 1)
    assert (sc_sort.isSortConstructor())
    try:
        Sort(solver).isSortConstructor()
    except RuntimeError:
        pytest.fail()


def test_is_first_class(solver):
    fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                     solver.getIntegerSort())
    assert (solver.getIntegerSort().isFirstClass())
    assert (fun_sort.isFirstClass())
    reSort = solver.getRegExpSort()
    assert (not reSort.isFirstClass())
    try:
        Sort(solver).isFirstClass()
    except RuntimeError:
        pytest.fail()


def test_is_function_like(solver):
    fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                     solver.getIntegerSort())
    assert (not solver.getIntegerSort().isFunctionLike())
    assert (fun_sort.isFunctionLike())

    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0][1].getSelectorTerm().getSort()
    assert (cons_sort.isFunctionLike())

    try:
        Sort(solver).isFunctionLike()
    except RuntimeError:
        pytest.fail()


def test_is_subsort_of(solver):
    assert (solver.getIntegerSort().isSubsortOf(solver.getIntegerSort()))
    assert (solver.getIntegerSort().isSubsortOf(solver.getRealSort()))
    assert (not solver.getIntegerSort().isSubsortOf(solver.getBooleanSort()))
    try:
        Sort(solver).isSubsortOf(Sort(solver))
    except RuntimeError:
        pytest.fail()


def test_is_comparable_to(solver):
    assert (solver.getIntegerSort().isComparableTo(solver.getIntegerSort()))
    assert (solver.getIntegerSort().isComparableTo(solver.getRealSort()))
    assert (not solver.getIntegerSort().isComparableTo(
        solver.getBooleanSort()))
    try:
        Sort(solver).isComparableTo(Sort(solver))
    except RuntimeError:
        pytest.fail()


def test_get_datatype(solver):
    dtypeSort = create_datatype_sort(solver)
    try:
        dtypeSort.getDatatype()
    except RuntimeError:
        pytest.fail()
    # create bv sort, check should fail
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getDatatype()


def test_datatype_sorts(solver):
    intSort = solver.getIntegerSort()
    dtypeSort = create_datatype_sort(solver)
    dt = dtypeSort.getDatatype()
    assert (not dtypeSort.isConstructor())
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
    assert (consSort.isConstructor())
    assert (not consSort.isTester())
    assert (not consSort.isSelector())
    assert (consSort.getConstructorArity() == 2)
    consDomSorts = consSort.getConstructorDomainSorts()
    assert (consDomSorts[0] == intSort)
    assert (consDomSorts[1] == dtypeSort)
    assert (consSort.getConstructorCodomainSort() == dtypeSort)

    # get tester
    isConsTerm = dcons.getTesterTerm()
    assert (isConsTerm.getSort().isTester())
    booleanSort = solver.getBooleanSort()

    assert (isConsTerm.getSort().getTesterDomainSort() == dtypeSort)
    assert (isConsTerm.getSort().getTesterCodomainSort() == booleanSort)
    with pytest.raises(RuntimeError):
        booleanSort.getTesterDomainSort()
    with pytest.raises(RuntimeError):
        booleanSort.getTesterCodomainSort()

    # get selector
    dselTail = dcons[1]
    tailTerm = dselTail.getSelectorTerm()
    assert (tailTerm.getSort().isSelector())
    assert (tailTerm.getSort().getSelectorDomainSort() == dtypeSort)
    assert (tailTerm.getSort().getSelectorCodomainSort() == dtypeSort)
    with pytest.raises(RuntimeError):
        booleanSort.getSelectorDomainSort()
    with pytest.raises(RuntimeError):
        booleanSort.getSelectorCodomainSort()


def test_instantiate(solver):
    # instantiate parametric datatype, check should not fail
    paramDtypeSort = create_param_datatype_sort(solver)
    try:
        paramDtypeSort.instantiate([solver.getIntegerSort()])
    except RuntimeError:
        pytest.fail()
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
    try:
        funSort.getFunctionArity()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionArity()


def test_get_function_domain_sorts(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    try:
        funSort.getFunctionDomainSorts()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionDomainSorts()


def test_get_function_codomain_sort(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    try:
        funSort.getFunctionCodomainSort()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionCodomainSort()


def test_get_array_index_sort(solver):
    elementSort = solver.mkBitVectorSort(32)
    indexSort = solver.mkBitVectorSort(32)
    arraySort = solver.mkArraySort(indexSort, elementSort)
    try:
        arraySort.getArrayIndexSort()
    except RuntimeError:
        pytest.fail()
    with pytest.raises(RuntimeError):
        indexSort.getArrayIndexSort()


def test_get_array_element_sort(solver):
    elementSort = solver.mkBitVectorSort(32)
    indexSort = solver.mkBitVectorSort(32)
    arraySort = solver.mkArraySort(indexSort, elementSort)
    try:
        arraySort.getArrayElementSort()
    except RuntimeError:
        pytest.fail()
    with pytest.raises(RuntimeError):
        indexSort.getArrayElementSort()


def test_get_set_element_sort(solver):
    setSort = solver.mkSetSort(solver.getIntegerSort())
    try:
        setSort.getSetElementSort()
    except RuntimeError:
        pytest.fail()
    elementSort = setSort.getSetElementSort()
    assert (elementSort == solver.getIntegerSort())
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSetElementSort()


def test_get_bag_element_sort(solver):
    bagSort = solver.mkBagSort(solver.getIntegerSort())
    try:
        bagSort.getBagElementSort()
    except RuntimeError:
        pytest.fail()
    elementSort = bagSort.getBagElementSort()
    assert (elementSort == solver.getIntegerSort())
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getBagElementSort()


def test_get_sequence_element_sort(solver):
    seqSort = solver.mkSequenceSort(solver.getIntegerSort())
    assert (seqSort.isSequence())
    try:
        seqSort.getSequenceElementSort()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    assert (not bvSort.isSequence())
    with pytest.raises(RuntimeError):
        bvSort.getSequenceElementSort()


def test_get_uninterpreted_sort_name(solver):
    uSort = solver.mkUninterpretedSort("u")
    try:
        uSort.getUninterpretedSortName()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getUninterpretedSortName()


def test_is_uninterpreted_sort_parameterized(solver):
    uSort = solver.mkUninterpretedSort("u")
    assert (not uSort.isUninterpretedSortParameterized())
    sSort = solver.mkSortConstructorSort("s", 1)
    siSort = sSort.instantiate([uSort])
    assert (siSort.isUninterpretedSortParameterized())
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.isUninterpretedSortParameterized()


def test_get_uninterpreted_sort_paramsorts(solver):
    uSort = solver.mkUninterpretedSort("u")
    try:
        uSort.getUninterpretedSortParamSorts()
    except RuntimeError:
        pytest.fail()
    sSort = solver.mkSortConstructorSort("s", 2)
    siSort = sSort.instantiate([uSort, uSort])
    assert (len(siSort.getUninterpretedSortParamSorts()) == 2)
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getUninterpretedSortParamSorts()


def test_get_uninterpreted_sort_constructor_name(solver):
    sSort = solver.mkSortConstructorSort("s", 2)
    try:
        sSort.getSortConstructorName()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSortConstructorName()


def test_get_uninterpreted_sort_constructor_arity(solver):
    sSort = solver.mkSortConstructorSort("s", 2)
    try:
        sSort.getSortConstructorArity()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSortConstructorArity()


def test_get_bv_size(solver):
    bvSort = solver.mkBitVectorSort(32)
    try:
        bvSort.getBVSize()
    except RuntimeError:
        pytest.fail()
    setSort = solver.mkSetSort(solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getBVSize()


def test_get_fp_exponent_size(solver):
    if solver.supportsFloatingPoint():
        fpSort = solver.mkFloatingPointSort(4, 8)
        try:
            fpSort.getFPExponentSize()
        except RuntimeError:
            pytest.fail()
        setSort = solver.mkSetSort(solver.getIntegerSort())
        with pytest.raises(RuntimeError):
            setSort.getFPExponentSize()


def test_get_fp_significand_size(solver):
    if solver.supportsFloatingPoint():
        fpSort = solver.mkFloatingPointSort(4, 8)
        try:
            fpSort.getFPSignificandSize()
        except RuntimeError:
            pytest.fail()
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
    try:
        paramDtypeSort.getDatatypeParamSorts()
    except RuntimeError:
        pytest.fail()
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
    try:
        dtypeSort.getDatatypeArity()
    except RuntimeError:
        pytest.fail()
    # create bv sort, check should fail
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getDatatypeArity()


def test_get_tuple_length(solver):
    tupleSort = solver.mkTupleSort(
        [solver.getIntegerSort(),
         solver.getIntegerSort()])
    try:
        tupleSort.getTupleLength()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleLength()


def test_get_tuple_sorts(solver):
    tupleSort = solver.mkTupleSort(
        [solver.getIntegerSort(),
         solver.getIntegerSort()])
    try:
        tupleSort.getTupleSorts()
    except RuntimeError:
        pytest.fail()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleSorts()


def test_sort_compare(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    bvSort = solver.mkBitVectorSort(32)
    bvSort2 = solver.mkBitVectorSort(32)
    assert (bvSort >= bvSort2)
    assert (bvSort <= bvSort2)
    assert ((intSort > boolSort) != (intSort < boolSort))
    assert ((intSort > bvSort or intSort == bvSort) == (intSort >= bvSort))


def test_sort_subtyping(solver):
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    assert (intSort.isSubsortOf(realSort))
    assert (not realSort.isSubsortOf(intSort))
    assert (intSort.isComparableTo(realSort))
    assert (realSort.isComparableTo(intSort))

    arraySortII = solver.mkArraySort(intSort, intSort)
    arraySortIR = solver.mkArraySort(intSort, realSort)
    assert (not arraySortII.isComparableTo(intSort))
    # we do not support subtyping for arrays
    assert (not arraySortII.isComparableTo(arraySortIR))

    setSortI = solver.mkSetSort(intSort)
    setSortR = solver.mkSetSort(realSort)
    # we don't support subtyping for sets
    assert (not setSortI.isComparableTo(setSortR))
    assert (not setSortI.isSubsortOf(setSortR))
    assert (not setSortR.isComparableTo(setSortI))
    assert (not setSortR.isSubsortOf(setSortI))


def test_sort_scoped_tostring(solver):
    name = "uninterp-sort"
    bvsort8 = solver.mkBitVectorSort(8)
    uninterp_sort = solver.mkUninterpretedSort(name)
    assert (str(bvsort8) == "(_ BitVec 8)")
    assert (str(uninterp_sort) == name)
    solver2 = pycvc4.Solver()
    assert (str(bvsort8) == "(_ BitVec 8)")
    assert (str(uninterp_sort) == name)
