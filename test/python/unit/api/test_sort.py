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
    solver = pycvc4.Solver()
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
    assert(solver.getBooleanSort().isBoolean())
    try:
        Sort(solver).isBoolean()
    except RuntimeError:
        pytest.fail()


def test_is_integer(solver):
  assert(solver.getIntegerSort().isInteger())
  assert(not solver.getRealSort().isInteger())
  try:
      Sort(solver).isInteger()
  except RuntimeError:
      pytest.fail()


def test_is_real(solver):
  assert(solver.getRealSort().isReal())
  assert(not solver.getIntegerSort().isReal())
  try:
      Sort(solver).isReal()
  except RuntimeError:
      pytest.fail()


def test_is_string(solver):
  assert(solver.getStringSort().isString())
  try:
      Sort(solver).isString()
  except RuntimeError:
      pytest.fail()


def test_is_reg_exp(solver):
  assert(solver.getRegExpSort().isRegExp())
  try:
      Sort(solver).isRegExp()
  except RuntimeError:
      pytest.fail()


def test_is_rounding_mode(solver):
    if solver.supportsFloatingPoint():
        assert(solver.getRoundingModeSort().isRoundingMode())
        try:
            Sort(solver).isRoundingMode()
        except RuntimeError:
            pytest.fail()


def test_is_bit_vector(solver):
  assert(solver.mkBitVectorSort(8).isBitVector())
  try:
      Sort(solver).isBitVector()
  except RuntimeError:
      pytest.fail()


def test_is_floating_point(solver):
    if solver.supportsFloatingPoint():
        assert(solver.mkFloatingPointSort(8, 24).isFloatingPoint())
        try:
            Sort(solver).isFloatingPoint()
        except RuntimeError:
            pytest.fail()


def test_is_datatype(solver):
  dt_sort = create_datatype_sort(solver)
  assert(dt_sort.isDatatype())
  try:
      Sort(solver).isDatatype()
  except RuntimeError:
      pytest.fail()


def test_is_parametric_datatype(solver):
  param_dt_sort = create_param_datatype_sort(solver)
  assert(param_dt_sort.isParametricDatatype())
  try:
      Sort(solver).isParametricDatatype()
  except RuntimeError:
      pytest.fail()


def test_is_constructor(solver):
  dt_sort = create_datatype_sort(solver)
  dt = dt_sort.getDatatype()
  cons_sort = dt[0].getConstructorTerm().getSort()
  assert(cons_sort.isConstructor())
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
  assert(cons_sort.isSelector())
  try:
      Sort(solver).isSelector()
  except RuntimeError:
      pytest.fail()


def test_is_tester(solver):
  dt_sort = create_datatype_sort(solver)
  dt = dt_sort.getDatatype()
  cons_sort = dt[0].getTesterTerm().getSort()
  assert(cons_sort.isTester())
  try:
      Sort(solver).isTester()
  except RuntimeError:
      pytest.fail()


def test_is_function(solver):
  fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                          solver.getIntegerSort())
  assert(fun_sort.isFunction())
  try:
      Sort(solver).isFunction()
  except RuntimeError:
      pytest.fail()


def test_is_predicate(solver):
  pred_sort = solver.mkPredicateSort(solver.getRealSort())
  assert(pred_sort.isPredicate())
  try:
      Sort(solver).isPredicate()
  except RuntimeError:
      pytest.fail()


def test_is_tuple(solver):
  tup_sort = solver.mkTupleSort(solver.getRealSort())
  assert(tup_sort.isTuple())
  try:
      Sort(solver).isTuple()
  except RuntimeError:
      pytest.fail()


def test_is_record(solver):
  rec_sort = solver.mkRecordSort([("asdf", solver.getRealSort())])
  assert(rec_sort.isRecord())
  try:
      Sort(solver).isRecord()
  except RuntimeError:
      pytest.fail()


def test_is_array(solver):
  arr_sort = solver.mkArraySort(solver.getRealSort(), solver.getIntegerSort())
  assert(arr_sort.isArray())
  try:
      Sort(solver).isArray()
  except RuntimeError:
      pytest.fail()


def test_is_set(solver):
  set_sort = solver.mkSetSort(solver.getRealSort())
  assert(set_sort.isSet())
  try:
      Sort(solver).isSet()
  except RuntimeError:
      pytest.fail()

#TODO missing api
#def test_is_bag(solver):
#  bag_sort = solver.mkBagSort(solver.getRealSort())
#  assert(bag_sort.isBag())
#  try:
#      Sort(solver).isBag()
#  except RuntimeError:
#      pytest.fail()


def test_is_sequence(solver):
  seq_sort = solver.mkSequenceSort(solver.getRealSort())
  assert(seq_sort.isSequence())
  try:
      Sort(solver).isSequence()
  except RuntimeError:
      pytest.fail()


def test_is_uninterpreted(solver):
  un_sort = solver.mkUninterpretedSort("asdf")
  assert(un_sort.isUninterpretedSort())
  try:
      Sort(solver).isUninterpretedSort()
  except RuntimeError:
      pytest.fail()


def test_is_sortconstructor(solver):
  sc_sort = solver.mkSortConstructorSort("asdf", 1)
  assert(sc_sort.isSortConstructor())
  try:
      Sort(solver).isSortConstructor()
  except RuntimeError:
      pytest.fail()


def test_is_firstclass(solver):
  fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                          solver.getIntegerSort())
  assert(solver.getIntegerSort().isFirstClass())
  assert(fun_sort.isFirstClass())
  reSort = solver.getRegExpSort()
  assert(not reSort.isFirstClass())
  try:
      Sort(solver).isFirstClass()
  except RuntimeError:
      pytest.fail()


def test_is_functionlike(solver):
  fun_sort = solver.mkFunctionSort(solver.getRealSort(),
                                          solver.getIntegerSort())
  assert(not solver.getIntegerSort().isFunctionLike())
  assert(fun_sort.isFunctionLike())

  dt_sort = create_datatype_sort(solver)
  dt = dt_sort.getDatatype()
  cons_sort = dt[0][1].getSelectorTerm().getSort()
  assert(cons_sort.isFunctionLike())

  try:
      Sort(solver).isFunctionLike()
  except RuntimeError:
      pytest.fail()


def test_is_subsortof(solver):
  assert(solver.getIntegerSort().isSubsortOf(solver.getIntegerSort()))
  assert(solver.getIntegerSort().isSubsortOf(solver.getRealSort()))
  assert(not solver.getIntegerSort().isSubsortOf(solver.getBooleanSort()))
  try:
      Sort(solver).isSubsortOf(Sort(solver))
  except RuntimeError:
      pytest.fail()


def test_is_comparableto(solver):
  assert(
      solver.getIntegerSort().isComparableTo(solver.getIntegerSort()))
  assert(solver.getIntegerSort().isComparableTo(solver.getRealSort()))
  assert(not solver.getIntegerSort().isComparableTo(solver.getBooleanSort()))
  try:
      Sort(solver).isComparableTo(Sort(solver))
  except RuntimeError:
      pytest.fail()






















#def testgetdatatype(solver):
#    dtypeSpec = solver.mkDatatypeDecl("list")
#    cons = solver.mkDatatypeConstructorDecl("cons")
#    cons.addSelector("head", solver.getIntegerSort())
#    dtypeSpec.addConstructor(cons)
#    nil = solver.mkDatatypeConstructorDecl("nil")
#    dtypeSpec.addConstructor(nil)
#    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
#
#    # expecting no Error
#    dtypeSort.getDatatype()
#
#    bvSort = solver.mkBitVectorSort(32)
#    with pytest.raises(Exception):
#        # expect an exception
#        bvSort.getDatatype()
#
#
#def testDatatypeSorts(solver):
#    solver = pycvc4.Solver()
#    intSort = solver.getIntegerSort()
#    # create datatype sort to test
#    dtypeSpec = solver.mkDatatypeDecl("list")
#    cons = solver.mkDatatypeConstructorDecl("cons")
#    cons.addSelector("head", intSort)
#    cons.addSelectorSelf("tail")
#    dtypeSpec.addConstructor(cons)
#    nil = solver.mkDatatypeConstructorDecl("nil")
#    dtypeSpec.addConstructor(nil)
#    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
#    dt = dtypeSort.getDatatype()
#    assert not dtypeSort.isConstructor()
#
#    with pytest.raises(Exception):
#        dtypeSort.getConstructorCodomainSort()
#
#    with pytest.raises(Exception):
#        dtypeSort.getConstructorDomainSorts()
#
#    with pytest.raises(Exception):
#        dtypeSort.getConstructorArity()
#
#    # get constructor
#    dcons = dt[0]
#    consTerm = dcons.getConstructorTerm()
#    consSort = consTerm.getSort()
#    assert consSort.isConstructor()
#    assert not consSort.isTester()
#    assert not consSort.isSelector()
#    assert consSort.getConstructorArity() == 2
#    consDomSorts = consSort.getConstructorDomainSorts()
#    assert consDomSorts[0] == intSort
#    assert consDomSorts[1] == dtypeSort
#    assert consSort.getConstructorCodomainSort() == dtypeSort
#
#    # get tester
#    isConsTerm = dcons.getTesterTerm()
#    assert isConsTerm.getSort().isTester()
#
#    # get selector
#    dselTail = dcons[1]
#    tailTerm = dselTail.getSelectorTerm()
#    assert tailTerm.getSort().isSelector()
#
#
#def testInstantiate(solver):
#    solver = pycvc4.Solver()
#    # instantiate parametric datatype, check should not fail
#    sort = solver.mkParamSort("T")
#    paramDtypeSpec = solver.mkDatatypeDecl("paramlist", sort)
#    paramCons = solver.mkDatatypeConstructorDecl("cons")
#    paramNil = solver.mkDatatypeConstructorDecl("nil")
#    paramCons.addSelector("head", sort)
#    paramDtypeSpec.addConstructor(paramCons)
#    paramDtypeSpec.addConstructor(paramNil)
#    paramDtypeSort = solver.mkDatatypeSort(paramDtypeSpec)
#    paramDtypeSort.instantiate([solver.getIntegerSort()])
#
#    # instantiate non-parametric datatype sort, check should fail
#    dtypeSpec = solver.mkDatatypeDecl("list")
#    cons = solver.mkDatatypeConstructorDecl("cons")
#    cons.addSelector("head", solver.getIntegerSort())
#    dtypeSpec.addConstructor(cons)
#    nil = solver.mkDatatypeConstructorDecl("nil")
#    dtypeSpec.addConstructor(nil)
#    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
#
#    with pytest.raises(Exception):
#        dtypeSort.instantiate([solver.getIntegerSort()])
#
#
#def testGetFunctionArity(solver):
#    solver = pycvc4.Solver()
#    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
#                                            solver.getIntegerSort())
#    funSort.getFunctionArity()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getFunctionArity()
#
#
#def testGetFunctionDomainSorts(solver):
#    solver = pycvc4.Solver()
#    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
#                                            solver.getIntegerSort())
#    funSort.getFunctionDomainSorts()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getFunctionDomainSorts()
#
#
#def testGetFunctionCodomainSort(solver):
#    solver = pycvc4.Solver()
#    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
#                                            solver.getIntegerSort())
#    funSort.getFunctionCodomainSort()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getFunctionCodomainSort()
#
#def testGetArrayIndexSort(solver):
#    solver = pycvc4.Solver()
#    elementSort = solver.mkBitVectorSort(32)
#    indexSort = solver.mkBitVectorSort(32)
#    arraySort = solver.mkArraySort(indexSort, elementSort)
#    arraySort.getArrayIndexSort()
#
#    with pytest.raises(Exception):
#        indexSort.getArrayIndexSort()
#
#def testGetArrayElementSort(solver):
#    solver = pycvc4.Solver()
#    elementSort = solver.mkBitVectorSort(32)
#    indexSort = solver.mkBitVectorSort(32)
#    arraySort = solver.mkArraySort(indexSort, elementSort)
#    arraySort.getArrayElementSort()
#
#    with pytest.raises(Exception):
#        indexSort.getArrayElementSort()
#
#def testGetSetElementSort(solver):
#    solver = pycvc4.Solver()
#    setSort = solver.mkSetSort(solver.getIntegerSort())
#    setSort.getSetElementSort()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getSetElementSort()
#
#def testGetSequenceElementSort(solver):
#    solver = pycvc4.Solver()
#    seqSort = solver.mkSequenceSort(solver.getIntegerSort())
#    seqSort.getSequenceElementSort()
#    bvSort = solver.mkBitVectorSort(32)
#    assert not bvSort.isSequence()
#
#    with pytest.raises(Exception):
#        bvSort.getSetElementSort()
#
#def testGetUninterpretedSortName(solver):
#    solver = pycvc4.Solver()
#    uSort = solver.mkUninterpretedSort("u")
#    uSort.getUninterpretedSortName()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getUninterpretedSortName()
#
#def testIsUninterpretedSortParameterized(solver):
#    solver = pycvc4.Solver()
#    uSort = solver.mkUninterpretedSort("u")
#    uSort.isUninterpretedSortParameterized()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.isUninterpretedSortParameterized()
#
#def testGetUninterpretedSortParamSorts(solver):
#    solver = pycvc4.Solver()
#    uSort = solver.mkUninterpretedSort("u")
#    uSort.getUninterpretedSortParamSorts()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getUninterpretedSortParamSorts()
#
#def testGetUninterpretedSortConstructorName(solver):
#    solver = pycvc4.Solver()
#    sSort = solver.mkSortConstructorSort("s", 2)
#    sSort.getSortConstructorName()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getSortConstructorName()
#
#def testGetUninterpretedSortConstructorArity(solver):
#    solver = pycvc4.Solver()
#    sSort = solver.mkSortConstructorSort("s", 2)
#    sSort.getSortConstructorArity()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getSortConstructorArity()
#
#def testGetBVSize(solver):
#    solver = pycvc4.Solver()
#    bvSort = solver.mkBitVectorSort(32)
#    bvSort.getBVSize()
#    setSort = solver.mkSetSort(solver.getIntegerSort())
#
#    with pytest.raises(Exception):
#        setSort.getBVSize()
#
#def testGetFPExponentSize(solver):
#    solver = pycvc4.Solver()
#
#    if solver.supportsFloatingPoint(solver):
#        fpSort = solver.mkFloatingPointSort(4, 8)
#        fpSort.getFPExponentSize()
#        setSort = solver.mkSetSort(solver.getIntegerSort())
#
#        with pytest.raises(Exception):
#            setSort.getFPExponentSize()
#    else:
#        with pytest.raises(Exception):
#            solver.mkFloatingPointSort(4, 8)
#
#def testGetFPSignificandSize(solver):
#    solver = pycvc4.Solver()
#
#    if solver.supportsFloatingPoint(solver):
#        fpSort = solver.mkFloatingPointSort(4, 8)
#        fpSort.getFPSignificandSize()
#        setSort = solver.mkSetSort(solver.getIntegerSort())
#
#        with pytest.raises(Exception):
#            setSort.getFPSignificandSize()
#    else:
#        with pytest.raises(Exception):
#            solver.mkFloatingPointSort(4, 8)
#
#def testGetDatatypeParamSorts(solver):
#    solver = pycvc4.Solver()
#    # create parametric datatype, check should not fail
#    sort = solver.mkParamSort("T")
#    paramDtypeSpec = solver.mkDatatypeDecl("paramlist", sort)
#    paramCons = solver.mkDatatypeConstructorDecl("cons")
#    paramNil = solver.mkDatatypeConstructorDecl("nil")
#    paramCons.addSelector("head", sort)
#    paramDtypeSpec.addConstructor(paramCons)
#    paramDtypeSpec.addConstructor(paramNil)
#    paramDtypeSort = solver.mkDatatypeSort(paramDtypeSpec)
#    paramDtypeSort.getDatatypeParamSorts()
#    # create non-parametric datatype sort, check should fail
#    dtypeSpec = solver.mkDatatypeDecl("list")
#    cons = solver.mkDatatypeConstructorDecl("cons")
#    cons.addSelector("head", solver.getIntegerSort())
#    dtypeSpec.addConstructor(cons)
#    nil = solver.mkDatatypeConstructorDecl("nil")
#    dtypeSpec.addConstructor(nil)
#    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
#
#    with pytest.raises(Exception):
#        dtypeSort.getDatatypeParamSorts()
#
#
#def testGetDatatypeArity(solver):
#    solver = pycvc4.Solver()
#    # create datatype sort, check should not fail
#    dtypeSpec = solver.mkDatatypeDecl("list")
#    cons = solver.mkDatatypeConstructorDecl("cons")
#    cons.addSelector("head", solver.getIntegerSort())
#    dtypeSpec.addConstructor(cons)
#    nil = solver.mkDatatypeConstructorDecl("nil")
#    dtypeSpec.addConstructor(nil)
#    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
#    dtypeSort.getDatatypeArity()
#    # create bv sort, check should fail
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getDatatypeArity()
#
#def testGetTupleLength(solver):
#    solver = pycvc4.Solver()
#    tupleSort = solver.mkTupleSort([solver.getIntegerSort(), solver.getIntegerSort()])
#    tupleSort.getTupleLength()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getTupleLength()
#
#def testGetTupleSorts(solver):
#    solver = pycvc4.Solver()
#    tupleSort = solver.mkTupleSort([solver.getIntegerSort(), solver.getIntegerSort()])
#    tupleSort.getTupleSorts()
#    bvSort = solver.mkBitVectorSort(32)
#
#    with pytest.raises(Exception):
#        bvSort.getTupleSorts()
#
#def testSortCompare(solver):
#    solver = pycvc4.Solver()
#    boolSort = solver.getBooleanSort()
#    intSort = solver.getIntegerSort()
#    bvSort = solver.mkBitVectorSort(32)
#    bvSort2 = solver.mkBitVectorSort(32)
#    assert bvSort >= bvSort2
#    assert bvSort <= bvSort2
#    assert (intSort > boolSort) != (intSort < boolSort)
#    assert (intSort > bvSort or intSort == bvSort) == (intSort >= bvSort)
#
#def testSortSubtyping(solver):
#    solver = pycvc4.Solver()
#    intSort = solver.getIntegerSort()
#    realSort = solver.getRealSort()
#    assert intSort.isSubsortOf(realSort)
#    assert not realSort.isSubsortOf(intSort)
#    assert intSort.isComparableTo(realSort)
#    assert realSort.isComparableTo(intSort)
#
#    arraySortII = solver.mkArraySort(intSort, intSort)
#    arraySortIR = solver.mkArraySort(intSort, realSort)
#    assert not arraySortII.isComparableTo(intSort)
#    # we do not support subtyping for arrays
#    assert not arraySortII.isComparableTo(arraySortIR)
#
#    setSortI = solver.mkSetSort(intSort)
#    setSortR = solver.mkSetSort(realSort)
#    # we don't support subtyping for sets
#    assert not setSortI.isComparableTo(setSortR)
#    assert not setSortI.isSubsortOf(setSortR)
#    assert not setSortR.isComparableTo(setSortI)
#    assert not setSortR.isSubsortOf(setSortI)
#
