###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Makai Mann
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
import cvc5
from cvc5 import Kind, SortKind, Sort


@pytest.fixture
def solver():
    return cvc5.Solver()


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
    paramDtypeSpec = solver.mkDatatypeDecl("paramlist", [sort])
    paramCons = solver.mkDatatypeConstructorDecl("cons")
    paramNil = solver.mkDatatypeConstructorDecl("nil")
    paramCons.addSelector("head", sort)
    paramDtypeSpec.addConstructor(paramCons)
    paramDtypeSpec.addConstructor(paramNil)
    paramDtypeSort = solver.mkDatatypeSort(paramDtypeSpec)
    return paramDtypeSort


def test_hash(solver):
    hash(solver.getIntegerSort())


def test_operators_comparison(solver):
    solver.getIntegerSort() == Sort(solver)
    solver.getIntegerSort() != Sort(solver)
    solver.getIntegerSort() < Sort(solver)
    solver.getIntegerSort() <= Sort(solver)
    solver.getIntegerSort() > Sort(solver)
    solver.getIntegerSort() >= Sort(solver)

def test_get_kind(solver):
    b = solver.getBooleanSort()
    dt_sort = create_datatype_sort(solver)
    arr_sort = solver.mkArraySort(solver.getRealSort(), solver.getIntegerSort())
    assert b.getKind() == SortKind.BOOLEAN_SORT
    assert dt_sort.getKind()== SortKind.DATATYPE_SORT
    assert arr_sort.getKind()== SortKind.ARRAY_SORT

def test_has_get_symbol(solver):
    n = Sort(solver)
    b = solver.getBooleanSort()
    s0 = solver.mkParamSort("s0")
    s1 = solver.mkParamSort("|s1\\|")

    with pytest.raises(RuntimeError):
        n.hasSymbol()
    assert not b.hasSymbol()
    assert s0.hasSymbol()
    assert s1.hasSymbol()

    with pytest.raises(RuntimeError):
        n.getSymbol()
    with pytest.raises(RuntimeError):
        b.getSymbol()
    assert s0.getSymbol() == "s0"
    assert s1.getSymbol() == "|s1\\|"


def test_is_null(solver):
   x = Sort(solver)
   assert x.isNull()
   x = solver.getBooleanSort()
   assert not x.isNull()

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
    assert solver.getRoundingModeSort().isRoundingMode()
    Sort(solver).isRoundingMode()


def test_is_bit_vector(solver):
    assert solver.mkBitVectorSort(8).isBitVector()
    Sort(solver).isBitVector()


def test_is_floating_point(solver):
    assert solver.mkFloatingPointSort(8, 24).isFloatingPoint()
    Sort(solver).isFloatingPoint()


def test_is_datatype(solver):
    dt_sort = create_datatype_sort(solver)
    assert dt_sort.isDatatype()
    Sort(solver).isDatatype()


def test_is_constructor(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getTerm().getSort()
    assert cons_sort.isDatatypeConstructor()
    Sort(solver).isDatatypeConstructor()


def test_is_selector(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    dt0 = dt[0]
    dt01 = dt0[1]
    cons_sort = dt01.getTerm().getSort()
    assert cons_sort.isDatatypeSelector()
    Sort(solver).isDatatypeSelector()


def test_is_tester(solver):
    dt_sort = create_datatype_sort(solver)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getTesterTerm().getSort()
    assert cons_sort.isDatatypeTester()
    Sort(solver).isDatatypeTester()

def test_is_updater(solver):
  dt_sort = create_datatype_sort(solver)
  dt = dt_sort.getDatatype()
  updater_sort = dt[0][0].getUpdaterTerm().getSort()
  assert updater_sort.isDatatypeUpdater()
  Sort(solver).isDatatypeUpdater()

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
    rec_sort = solver.mkRecordSort(("asdf", solver.getRealSort()))
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


def test_is_abstract(solver):
  assert solver.mkAbstractSort(SortKind.BITVECTOR_SORT).isAbstract()
  assert not solver.mkAbstractSort(SortKind.ARRAY_SORT).isAbstract()
  assert solver.mkAbstractSort(SortKind.ABSTRACT_SORT).isAbstract()
  Sort(solver).isAbstract()


def test_is_uninterpreted(solver):
    un_sort = solver.mkUninterpretedSort("asdf")
    assert un_sort.isUninterpretedSort()
    Sort(solver).isUninterpretedSort()


def test_is_sort_constructor(solver):
    sc_sort = solver.mkUninterpretedSortConstructorSort(1, "asdf")
    assert sc_sort.isUninterpretedSortConstructor()
    Sort(solver).isUninterpretedSortConstructor()


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
    assert not dtypeSort.isDatatypeConstructor()
    with pytest.raises(RuntimeError):
        dtypeSort.getDatatypeConstructorCodomainSort()
    with pytest.raises(RuntimeError):
        dtypeSort.getDatatypeConstructorDomainSorts()
    with pytest.raises(RuntimeError):
        dtypeSort.getDatatypeConstructorArity()

    # get constructor
    dcons = dt[0]
    consTerm = dcons.getTerm()
    consSort = consTerm.getSort()
    assert consSort.isDatatypeConstructor()
    assert not consSort.isDatatypeTester()
    assert not consSort.isDatatypeSelector()
    assert consSort.getDatatypeConstructorArity() == 2
    consDomSorts = consSort.getDatatypeConstructorDomainSorts()
    assert consDomSorts[0] == intSort
    assert consDomSorts[1] == dtypeSort
    assert consSort.getDatatypeConstructorCodomainSort() == dtypeSort

    # get tester
    isConsTerm = dcons.getTesterTerm()
    assert isConsTerm.getSort().isDatatypeTester()
    booleanSort = solver.getBooleanSort()

    assert isConsTerm.getSort().getDatatypeTesterDomainSort() == dtypeSort
    assert isConsTerm.getSort().getDatatypeTesterCodomainSort() == booleanSort
    with pytest.raises(RuntimeError):
        booleanSort.getDatatypeTesterDomainSort()
    with pytest.raises(RuntimeError):
        booleanSort.getDatatypeTesterCodomainSort()

    # get selector
    dselTail = dcons[1]
    tailTerm = dselTail.getTerm()
    assert tailTerm.getSort().isDatatypeSelector()
    assert tailTerm.getSort().getDatatypeSelectorDomainSort() == dtypeSort
    assert tailTerm.getSort().getDatatypeSelectorCodomainSort() == dtypeSort
    with pytest.raises(RuntimeError):
        booleanSort.getDatatypeSelectorDomainSort()
    with pytest.raises(RuntimeError):
        booleanSort.getDatatypeSelectorCodomainSort()


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
    # instantiate uninterpreted sort constructor
    sortConsSort = solver.mkUninterpretedSortConstructorSort(1, "s")
    sortConsSort.instantiate([solver.getIntegerSort()])

def test_is_instantiated(solver):
    paramDtypeSort = create_param_datatype_sort(solver)
    assert not paramDtypeSort.isInstantiated()
    instParamDtypeSort = paramDtypeSort.instantiate([solver.getIntegerSort()]);
    assert instParamDtypeSort.isInstantiated()

    sortConsSort = solver.mkUninterpretedSortConstructorSort(1, "s")
    assert not sortConsSort.isInstantiated()
    instSortConsSort = sortConsSort.instantiate([solver.getIntegerSort()])
    assert instSortConsSort.isInstantiated()

    assert not solver.getIntegerSort().isInstantiated()
    assert not solver.mkBitVectorSort(32).isInstantiated()

def test_get_instantiated_parameters(solver):
    intSort  = solver.getIntegerSort()
    realSort = solver.getRealSort()
    boolSort = solver.getBooleanSort()
    bvSort = solver.mkBitVectorSort(8)

    # parametric datatype instantiation
    p1 = solver.mkParamSort("p1")
    p2 = solver.mkParamSort("p2")
    pspec = solver.mkDatatypeDecl("pdtype", [p1, p2])
    pcons1 = solver.mkDatatypeConstructorDecl("cons1")
    pcons2 = solver.mkDatatypeConstructorDecl("cons2")
    pnil = solver.mkDatatypeConstructorDecl("nil")
    pcons1.addSelector("sel", p1)
    pcons2.addSelector("sel", p2)
    pspec.addConstructor(pcons1)
    pspec.addConstructor(pcons2)
    pspec.addConstructor(pnil)
    paramDtypeSort = solver.mkDatatypeSort(pspec)

    with pytest.raises(RuntimeError):
        paramDtypeSort.getInstantiatedParameters()

    instParamDtypeSort = \
        paramDtypeSort.instantiate([realSort, boolSort]);

    instSorts = instParamDtypeSort.getInstantiatedParameters();
    assert instSorts[0] == realSort
    assert instSorts[1] == boolSort

    # uninterpreted sort constructor sort instantiation
    sortConsSort = solver.mkUninterpretedSortConstructorSort(4, "s")
    with pytest.raises(RuntimeError):
        sortConsSort.getInstantiatedParameters()

    instSortConsSort = sortConsSort.instantiate(
        [boolSort, intSort, bvSort, realSort]);

    instSorts = instSortConsSort.getInstantiatedParameters()
    assert instSorts[0] == boolSort
    assert instSorts[1] == intSort
    assert instSorts[2] == bvSort
    assert instSorts[3] == realSort

    with pytest.raises(RuntimeError):
        intSort.getInstantiatedParameters()
    with pytest.raises(RuntimeError):
        bvSort.getInstantiatedParameters()

def test_get_uninterpreted_sort_constructor(solver):
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    boolSort = solver.getBooleanSort()
    bvSort = solver.mkBitVectorSort(8)
    sortConsSort = solver.mkUninterpretedSortConstructorSort(4, "s")
    with pytest.raises(RuntimeError):
        sortConsSort.getUninterpretedSortConstructor()
    instSortConsSort = \
        sortConsSort.instantiate([boolSort, intSort, bvSort, realSort]);
    assert sortConsSort == instSortConsSort.getUninterpretedSortConstructor()

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


def test_get_abstract_kind(solver):
    assert solver.mkAbstractSort(SortKind.BITVECTOR_SORT).getAbstractedKind() == SortKind.BITVECTOR_SORT
    with pytest.raises(RuntimeError):
        solver.mkAbstractSort(SortKind.ARRAY_SORT).getAbstractedKind()
    assert solver.mkAbstractSort(SortKind.ABSTRACT_SORT).getAbstractedKind() == SortKind.ABSTRACT_SORT


def test_get_uninterpreted_sort_name(solver):
    uSort = solver.mkUninterpretedSort("u")
    uSort.getSymbol()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSymbol()


def test_get_uninterpreted_sort_constructor_name(solver):
    sSort = solver.mkUninterpretedSortConstructorSort(2, "s")
    sSort.getSymbol()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSymbol()


def test_get_uninterpreted_sort_constructor_arity(solver):
    sSort = solver.mkUninterpretedSortConstructorSort(2, "s")
    sSort.getUninterpretedSortConstructorArity()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getUninterpretedSortConstructorArity()


def test_get_bv_size(solver):
    bvSort = solver.mkBitVectorSort(32)
    bvSort.getBitVectorSize()
    setSort = solver.mkSetSort(solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getBitVectorSize()


def test_get_fp_exponent_size(solver):
    fpSort = solver.mkFloatingPointSort(4, 8)
    fpSort.getFloatingPointExponentSize()
    setSort = solver.mkSetSort(solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getFloatingPointExponentSize()


def test_get_fp_significand_size(solver):
    fpSort = solver.mkFloatingPointSort(4, 8)
    fpSort.getFloatingPointSignificandSize()
    setSort = solver.mkSetSort(solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getFloatingPointSignificandSize()


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
        solver.getIntegerSort(),
        solver.getIntegerSort())
    tupleSort.getTupleLength()
    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleLength()


def test_get_tuple_sorts(solver):
    tupleSort = solver.mkTupleSort(
        solver.getIntegerSort(),
        solver.getIntegerSort())
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


def test_sort_scoped_tostring(solver):
    name = "uninterp-sort"
    bvsort8 = solver.mkBitVectorSort(8)
    uninterp_sort = solver.mkUninterpretedSort(name)
    assert str(bvsort8) == "(_ BitVec 8)"
    assert str(uninterp_sort) == name
    solver2 = cvc5.Solver()
    assert str(bvsort8) == "(_ BitVec 8)"
    assert str(uninterp_sort) == name
