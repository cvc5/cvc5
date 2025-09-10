###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Yoni Zohar, Makai Mann
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
def tm():
    return cvc5.TermManager()


def create_datatype_sort(tm):
    intSort = tm.getIntegerSort()
    # create datatype sort to test
    dtypeSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = tm.mkDatatypeSort(dtypeSpec)
    return dtypeSort


def create_param_datatype_sort(tm):
    sort = tm.mkParamSort("T")
    paramDtypeSpec = tm.mkDatatypeDecl("paramlist", [sort])
    paramCons = tm.mkDatatypeConstructorDecl("cons")
    paramNil = tm.mkDatatypeConstructorDecl("nil")
    paramCons.addSelector("head", sort)
    paramDtypeSpec.addConstructor(paramCons)
    paramDtypeSpec.addConstructor(paramNil)
    paramDtypeSort = tm.mkDatatypeSort(paramDtypeSpec)
    return paramDtypeSort


def test_hash(tm):
    hash(tm.getIntegerSort())


def test_operators_comparison(tm):
    assert tm.getIntegerSort() == tm.getIntegerSort()
    assert tm.getIntegerSort() != tm.getBooleanSort()
    assert not tm.getIntegerSort() < tm.getIntegerSort()
    assert tm.getIntegerSort() <= tm.getIntegerSort()
    assert not tm.getIntegerSort() > tm.getIntegerSort()
    assert tm.getIntegerSort() >= tm.getIntegerSort()

def test_get_kind(tm):
    b = tm.getBooleanSort()
    dt_sort = create_datatype_sort(tm)
    arr_sort = tm.mkArraySort(tm.getRealSort(), tm.getIntegerSort())
    assert b.getKind() == SortKind.BOOLEAN_SORT
    assert dt_sort.getKind()== SortKind.DATATYPE_SORT
    assert arr_sort.getKind()== SortKind.ARRAY_SORT

def test_has_get_symbol(tm):
    b = tm.getBooleanSort()
    s0 = tm.mkParamSort("s0")
    s1 = tm.mkParamSort("|s1\\|")
    assert not b.hasSymbol()
    assert s0.hasSymbol()
    assert s1.hasSymbol()
    with pytest.raises(RuntimeError):
        b.getSymbol()
    assert s0.getSymbol() == "s0"
    assert s1.getSymbol() == "|s1\\|"


def test_is_null(tm):
   x = tm.getBooleanSort()
   assert not x.isNull()

def test_is_boolean(tm):
    assert tm.getBooleanSort().isBoolean()


def test_is_integer(tm):
    assert tm.getIntegerSort().isInteger()
    assert not tm.getRealSort().isInteger()


def test_is_real(tm):
    assert tm.getRealSort().isReal()
    assert not tm.getIntegerSort().isReal()


def test_is_string(tm):
    assert tm.getStringSort().isString()


def test_is_reg_exp(tm):
    assert tm.getRegExpSort().isRegExp()


def test_is_rounding_mode(tm):
    assert tm.getRoundingModeSort().isRoundingMode()


def test_is_bit_vector(tm):
    assert tm.mkBitVectorSort(8).isBitVector()


def test_is_floating_point(tm):
    assert tm.mkFloatingPointSort(8, 24).isFloatingPoint()


def test_is_datatype(tm):
    dt_sort = create_datatype_sort(tm)
    assert dt_sort.isDatatype()


def test_is_constructor(tm):
    dt_sort = create_datatype_sort(tm)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getTerm().getSort()
    assert cons_sort.isDatatypeConstructor()


def test_is_selector(tm):
    dt_sort = create_datatype_sort(tm)
    dt = dt_sort.getDatatype()
    dt0 = dt[0]
    dt01 = dt0[1]
    cons_sort = dt01.getTerm().getSort()
    assert cons_sort.isDatatypeSelector()


def test_is_tester(tm):
    dt_sort = create_datatype_sort(tm)
    dt = dt_sort.getDatatype()
    cons_sort = dt[0].getTesterTerm().getSort()
    assert cons_sort.isDatatypeTester()

def test_is_updater(tm):
  dt_sort = create_datatype_sort(tm)
  dt = dt_sort.getDatatype()
  updater_sort = dt[0][0].getUpdaterTerm().getSort()
  assert updater_sort.isDatatypeUpdater()

def test_is_function(tm):
    fun_sort = tm.mkFunctionSort(tm.getRealSort(),
                                     tm.getIntegerSort())
    assert fun_sort.isFunction()


def test_is_predicate(tm):
    pred_sort = tm.mkPredicateSort(tm.getRealSort())
    assert pred_sort.isPredicate()


def test_is_tuple(tm):
    tup_sort = tm.mkTupleSort(tm.getRealSort())
    assert tup_sort.isTuple()


def test_is_nullable(tm):
    nullable_sort = tm.mkNullableSort(tm.getRealSort())
    assert nullable_sort.isNullable()


def test_is_record(tm):
    rec_sort = tm.mkRecordSort(("asdf", tm.getRealSort()))
    assert rec_sort.isRecord()


def test_is_array(tm):
    arr_sort = tm.mkArraySort(tm.getRealSort(),
                                  tm.getIntegerSort())
    assert arr_sort.isArray()


def test_is_set(tm):
    set_sort = tm.mkSetSort(tm.getRealSort())
    assert set_sort.isSet()


def test_is_bag(tm):
    bag_sort = tm.mkBagSort(tm.getRealSort())
    assert bag_sort.isBag()


def test_is_sequence(tm):
    seq_sort = tm.mkSequenceSort(tm.getRealSort())
    assert seq_sort.isSequence()


def test_is_abstract(tm):
  assert tm.mkAbstractSort(SortKind.BITVECTOR_SORT).isAbstract()
  assert not tm.mkAbstractSort(SortKind.ARRAY_SORT).isAbstract()
  assert tm.mkAbstractSort(SortKind.ABSTRACT_SORT).isAbstract()


def test_is_uninterpreted(tm):
    un_sort = tm.mkUninterpretedSort("asdf")
    assert un_sort.isUninterpretedSort()


def test_is_sort_constructor(tm):
    sc_sort = tm.mkUninterpretedSortConstructorSort(1, "asdf")
    assert sc_sort.isUninterpretedSortConstructor()


def test_get_datatype(tm):
    dtypeSort = create_datatype_sort(tm)
    dtypeSort.getDatatype()
    # create bv sort, check should fail
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getDatatype()


def test_datatype_sorts(tm):
    intSort = tm.getIntegerSort()
    dtypeSort = create_datatype_sort(tm)
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
    booleanSort = tm.getBooleanSort()

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


def test_instantiate(tm):
    # instantiate parametric datatype, check should not fail
    paramDtypeSort = create_param_datatype_sort(tm)
    paramDtypeSort.instantiate([tm.getIntegerSort()])
    # instantiate non-parametric datatype sort, check should fail
    dtypeSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", tm.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = tm.mkDatatypeSort(dtypeSpec)
    with pytest.raises(RuntimeError):
        dtypeSort.instantiate([tm.getIntegerSort()])
    # instantiate uninterpreted sort constructor
    sortConsSort = tm.mkUninterpretedSortConstructorSort(1, "s")
    sortConsSort.instantiate([tm.getIntegerSort()])

def test_is_instantiated(tm):
    paramDtypeSort = create_param_datatype_sort(tm)
    assert not paramDtypeSort.isInstantiated()
    instParamDtypeSort = paramDtypeSort.instantiate([tm.getIntegerSort()]);
    assert instParamDtypeSort.isInstantiated()

    sortConsSort = tm.mkUninterpretedSortConstructorSort(1, "s")
    assert not sortConsSort.isInstantiated()
    instSortConsSort = sortConsSort.instantiate([tm.getIntegerSort()])
    assert instSortConsSort.isInstantiated()

    assert not tm.getIntegerSort().isInstantiated()
    assert not tm.mkBitVectorSort(32).isInstantiated()

def test_get_instantiated_parameters(tm):
    intSort  = tm.getIntegerSort()
    realSort = tm.getRealSort()
    boolSort = tm.getBooleanSort()
    bvSort = tm.mkBitVectorSort(8)

    # parametric datatype instantiation
    p1 = tm.mkParamSort("p1")
    p2 = tm.mkParamSort("p2")
    pspec = tm.mkDatatypeDecl("pdtype", [p1, p2])
    pcons1 = tm.mkDatatypeConstructorDecl("cons1")
    pcons2 = tm.mkDatatypeConstructorDecl("cons2")
    pnil = tm.mkDatatypeConstructorDecl("nil")
    pcons1.addSelector("sel", p1)
    pcons2.addSelector("sel", p2)
    pspec.addConstructor(pcons1)
    pspec.addConstructor(pcons2)
    pspec.addConstructor(pnil)
    paramDtypeSort = tm.mkDatatypeSort(pspec)

    with pytest.raises(RuntimeError):
        paramDtypeSort.getInstantiatedParameters()

    instParamDtypeSort = \
        paramDtypeSort.instantiate([realSort, boolSort]);

    instSorts = instParamDtypeSort.getInstantiatedParameters();
    assert instSorts[0] == realSort
    assert instSorts[1] == boolSort

    # uninterpreted sort constructor sort instantiation
    sortConsSort = tm.mkUninterpretedSortConstructorSort(4, "s")
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

def test_get_uninterpreted_sort_constructor(tm):
    intSort = tm.getIntegerSort()
    realSort = tm.getRealSort()
    boolSort = tm.getBooleanSort()
    bvSort = tm.mkBitVectorSort(8)
    sortConsSort = tm.mkUninterpretedSortConstructorSort(4, "s")
    with pytest.raises(RuntimeError):
        sortConsSort.getUninterpretedSortConstructor()
    instSortConsSort = \
        sortConsSort.instantiate([boolSort, intSort, bvSort, realSort]);
    assert sortConsSort == instSortConsSort.getUninterpretedSortConstructor()

def test_get_function_arity(tm):
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),
                                    tm.getIntegerSort())
    funSort.getFunctionArity()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionArity()


def test_get_function_domain_sorts(tm):
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),
                                    tm.getIntegerSort())
    funSort.getFunctionDomainSorts()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionDomainSorts()


def test_get_function_codomain_sort(tm):
    funSort = tm.mkFunctionSort(tm.mkUninterpretedSort("u"),
                                    tm.getIntegerSort())
    funSort.getFunctionCodomainSort()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getFunctionCodomainSort()


def test_get_array_index_sort(tm):
    elementSort = tm.mkBitVectorSort(32)
    indexSort = tm.mkBitVectorSort(32)
    arraySort = tm.mkArraySort(indexSort, elementSort)
    arraySort.getArrayIndexSort()
    with pytest.raises(RuntimeError):
        indexSort.getArrayIndexSort()


def test_get_array_element_sort(tm):
    elementSort = tm.mkBitVectorSort(32)
    indexSort = tm.mkBitVectorSort(32)
    arraySort = tm.mkArraySort(indexSort, elementSort)
    arraySort.getArrayElementSort()
    with pytest.raises(RuntimeError):
        indexSort.getArrayElementSort()


def test_get_set_element_sort(tm):
    setSort = tm.mkSetSort(tm.getIntegerSort())
    setSort.getSetElementSort()
    elementSort = setSort.getSetElementSort()
    assert elementSort == tm.getIntegerSort()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSetElementSort()


def test_get_bag_element_sort(tm):
    bagSort = tm.mkBagSort(tm.getIntegerSort())
    bagSort.getBagElementSort()
    elementSort = bagSort.getBagElementSort()
    assert elementSort == tm.getIntegerSort()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getBagElementSort()


def test_get_sequence_element_sort(tm):
    seqSort = tm.mkSequenceSort(tm.getIntegerSort())
    assert seqSort.isSequence()
    seqSort.getSequenceElementSort()
    bvSort = tm.mkBitVectorSort(32)
    assert not bvSort.isSequence()
    with pytest.raises(RuntimeError):
        bvSort.getSequenceElementSort()


def test_get_abstract_kind(tm):
    assert tm.mkAbstractSort(SortKind.BITVECTOR_SORT).getAbstractedKind() == SortKind.BITVECTOR_SORT
    with pytest.raises(RuntimeError):
        tm.mkAbstractSort(SortKind.ARRAY_SORT).getAbstractedKind()
    assert tm.mkAbstractSort(SortKind.ABSTRACT_SORT).getAbstractedKind() == SortKind.ABSTRACT_SORT


def test_get_uninterpreted_sort_name(tm):
    uSort = tm.mkUninterpretedSort("u")
    uSort.getSymbol()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSymbol()


def test_get_uninterpreted_sort_constructor_name(tm):
    sSort = tm.mkUninterpretedSortConstructorSort(2, "s")
    sSort.getSymbol()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getSymbol()


def test_get_uninterpreted_sort_constructor_arity(tm):
    sSort = tm.mkUninterpretedSortConstructorSort(2, "s")
    sSort.getUninterpretedSortConstructorArity()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getUninterpretedSortConstructorArity()


def test_get_bv_size(tm):
    bvSort = tm.mkBitVectorSort(32)
    bvSort.getBitVectorSize()
    setSort = tm.mkSetSort(tm.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getBitVectorSize()


def test_get_fp_exponent_size(tm):
    fpSort = tm.mkFloatingPointSort(4, 8)
    fpSort.getFloatingPointExponentSize()
    setSort = tm.mkSetSort(tm.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getFloatingPointExponentSize()


def test_get_fp_significand_size(tm):
    fpSort = tm.mkFloatingPointSort(4, 8)
    fpSort.getFloatingPointSignificandSize()
    setSort = tm.mkSetSort(tm.getIntegerSort())
    with pytest.raises(RuntimeError):
        setSort.getFloatingPointSignificandSize()


def test_get_datatype_arity(tm):
    # create datatype sort, check should not fail
    dtypeSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", tm.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = tm.mkDatatypeSort(dtypeSpec)
    dtypeSort.getDatatypeArity()
    # create bv sort, check should fail
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getDatatypeArity()


def test_get_tuple_length(tm):
    tupleSort = tm.mkTupleSort(
        tm.getIntegerSort(),
        tm.getIntegerSort())
    tupleSort.getTupleLength()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleLength()


def test_get_tuple_sorts(tm):
    tupleSort = tm.mkTupleSort(
        tm.getIntegerSort(),
        tm.getIntegerSort())
    tupleSort.getTupleSorts()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getTupleSorts()


def test_get_nullable_element_sort(tm):
    nullableSort = tm.mkNullableSort(tm.getIntegerSort())
    nullableSort.getNullableElementSort()
    elementSort = nullableSort.getNullableElementSort()
    assert elementSort == tm.getIntegerSort()
    bvSort = tm.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        bvSort.getNullableElementSort()


def test_sort_compare(tm):
    boolSort = tm.getBooleanSort()
    intSort = tm.getIntegerSort()
    bvSort = tm.mkBitVectorSort(32)
    bvSort2 = tm.mkBitVectorSort(32)
    assert bvSort >= bvSort2
    assert bvSort <= bvSort2
    assert (intSort > boolSort) != (intSort < boolSort)
    assert (intSort > bvSort or intSort == bvSort) == (intSort >= bvSort)


def test_sort_scoped_tostring(tm):
    name = "uninterp-sort"
    bvsort8 = tm.mkBitVectorSort(8)
    uninterp_sort = tm.mkUninterpretedSort(name)
    assert str(bvsort8) == "(_ BitVec 8)"
    assert str(uninterp_sort) == name
    assert str(bvsort8) == "(_ BitVec 8)"
    assert str(uninterp_sort) == name

def test_sort_substitute(tm):
    sortVar0 = tm.mkParamSort("T0")
    sortVar1 = tm.mkParamSort("T1")
    intSort = tm.getIntegerSort()
    realSort = tm.getRealSort()
    arraySort0 = tm.mkArraySort(sortVar0, sortVar0)
    arraySort1 = tm.mkArraySort(sortVar0, sortVar1)
    # Now create instantiations of the defined sorts
    arraySort0.substitute(sortVar0, intSort)
    arraySort1.substitute([sortVar0, sortVar1], [intSort, realSort])
