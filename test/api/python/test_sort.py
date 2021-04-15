###############################################################################
# Top contributors (to current version):
#   Makai Mann, Andres Noetzli, Mudathir Mohamed
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
from pycvc5 import kinds


def testGetDatatype():
    solver = pycvc5.Solver()
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)

    # expecting no Error
    dtypeSort.getDatatype()

    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(Exception):
        # expect an exception
        bvSort.getDatatype()


def testDatatypeSorts():
    solver = pycvc5.Solver()
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
    dt = dtypeSort.getDatatype()
    assert not dtypeSort.isConstructor()

    with pytest.raises(Exception):
        dtypeSort.getConstructorCodomainSort()

    with pytest.raises(Exception):
        dtypeSort.getConstructorDomainSorts()

    with pytest.raises(Exception):
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

    # get selector
    dselTail = dcons[1]
    tailTerm = dselTail.getSelectorTerm()
    assert tailTerm.getSort().isSelector()


def testInstantiate():
    solver = pycvc5.Solver()
    # instantiate parametric datatype, check should not fail
    sort = solver.mkParamSort("T")
    paramDtypeSpec = solver.mkDatatypeDecl("paramlist", sort)
    paramCons = solver.mkDatatypeConstructorDecl("cons")
    paramNil = solver.mkDatatypeConstructorDecl("nil")
    paramCons.addSelector("head", sort)
    paramDtypeSpec.addConstructor(paramCons)
    paramDtypeSpec.addConstructor(paramNil)
    paramDtypeSort = solver.mkDatatypeSort(paramDtypeSpec)
    paramDtypeSort.instantiate([solver.getIntegerSort()])

    # instantiate non-parametric datatype sort, check should fail
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)

    with pytest.raises(Exception):
        dtypeSort.instantiate([solver.getIntegerSort()])


def testGetFunctionArity():
    solver = pycvc5.Solver()
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                            solver.getIntegerSort())
    funSort.getFunctionArity()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getFunctionArity()


def testGetFunctionDomainSorts():
    solver = pycvc5.Solver()
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                            solver.getIntegerSort())
    funSort.getFunctionDomainSorts()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getFunctionDomainSorts()


def testGetFunctionCodomainSort():
    solver = pycvc5.Solver()
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                            solver.getIntegerSort())
    funSort.getFunctionCodomainSort()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getFunctionCodomainSort()

def testGetArrayIndexSort():
    solver = pycvc5.Solver()
    elementSort = solver.mkBitVectorSort(32)
    indexSort = solver.mkBitVectorSort(32)
    arraySort = solver.mkArraySort(indexSort, elementSort)
    arraySort.getArrayIndexSort()

    with pytest.raises(Exception):
        indexSort.getArrayIndexSort()

def testGetArrayElementSort():
    solver = pycvc5.Solver()
    elementSort = solver.mkBitVectorSort(32)
    indexSort = solver.mkBitVectorSort(32)
    arraySort = solver.mkArraySort(indexSort, elementSort)
    arraySort.getArrayElementSort()

    with pytest.raises(Exception):
        indexSort.getArrayElementSort()

def testGetSetElementSort():
    solver = pycvc5.Solver()
    setSort = solver.mkSetSort(solver.getIntegerSort())
    setSort.getSetElementSort()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getSetElementSort()

def testGetSequenceElementSort():
    solver = pycvc5.Solver()
    seqSort = solver.mkSequenceSort(solver.getIntegerSort())
    seqSort.getSequenceElementSort()
    bvSort = solver.mkBitVectorSort(32)
    assert not bvSort.isSequence()

    with pytest.raises(Exception):
        bvSort.getSetElementSort()

def testGetUninterpretedSortName():
    solver = pycvc5.Solver()
    uSort = solver.mkUninterpretedSort("u")
    uSort.getUninterpretedSortName()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getUninterpretedSortName()

def testIsUninterpretedSortParameterized():
    solver = pycvc5.Solver()
    uSort = solver.mkUninterpretedSort("u")
    uSort.isUninterpretedSortParameterized()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.isUninterpretedSortParameterized()

def testGetUninterpretedSortParamSorts():
    solver = pycvc5.Solver()
    uSort = solver.mkUninterpretedSort("u")
    uSort.getUninterpretedSortParamSorts()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getUninterpretedSortParamSorts()

def testGetUninterpretedSortConstructorName():
    solver = pycvc5.Solver()
    sSort = solver.mkSortConstructorSort("s", 2)
    sSort.getSortConstructorName()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getSortConstructorName()

def testGetUninterpretedSortConstructorArity():
    solver = pycvc5.Solver()
    sSort = solver.mkSortConstructorSort("s", 2)
    sSort.getSortConstructorArity()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getSortConstructorArity()

def testGetBVSize():
    solver = pycvc5.Solver()
    bvSort = solver.mkBitVectorSort(32)
    bvSort.getBVSize()
    setSort = solver.mkSetSort(solver.getIntegerSort())

    with pytest.raises(Exception):
        setSort.getBVSize()

def testGetFPExponentSize():
    solver = pycvc5.Solver()

    if solver.supportsFloatingPoint():
        fpSort = solver.mkFloatingPointSort(4, 8)
        fpSort.getFPExponentSize()
        setSort = solver.mkSetSort(solver.getIntegerSort())

        with pytest.raises(Exception):
            setSort.getFPExponentSize()
    else:
        with pytest.raises(Exception):
            solver.mkFloatingPointSort(4, 8)

def testGetFPSignificandSize():
    solver = pycvc5.Solver()

    if solver.supportsFloatingPoint():
        fpSort = solver.mkFloatingPointSort(4, 8)
        fpSort.getFPSignificandSize()
        setSort = solver.mkSetSort(solver.getIntegerSort())

        with pytest.raises(Exception):
            setSort.getFPSignificandSize()
    else:
        with pytest.raises(Exception):
            solver.mkFloatingPointSort(4, 8)

def testGetDatatypeParamSorts():
    solver = pycvc5.Solver()
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

    with pytest.raises(Exception):
        dtypeSort.getDatatypeParamSorts()


def testGetDatatypeArity():
    solver = pycvc5.Solver()
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

    with pytest.raises(Exception):
        bvSort.getDatatypeArity()

def testGetTupleLength():
    solver = pycvc5.Solver()
    tupleSort = solver.mkTupleSort([solver.getIntegerSort(), solver.getIntegerSort()])
    tupleSort.getTupleLength()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getTupleLength()

def testGetTupleSorts():
    solver = pycvc5.Solver()
    tupleSort = solver.mkTupleSort([solver.getIntegerSort(), solver.getIntegerSort()])
    tupleSort.getTupleSorts()
    bvSort = solver.mkBitVectorSort(32)

    with pytest.raises(Exception):
        bvSort.getTupleSorts()

def testSortCompare():
    solver = pycvc5.Solver()
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    bvSort = solver.mkBitVectorSort(32)
    bvSort2 = solver.mkBitVectorSort(32)
    assert bvSort >= bvSort2
    assert bvSort <= bvSort2
    assert (intSort > boolSort) != (intSort < boolSort)
    assert (intSort > bvSort or intSort == bvSort) == (intSort >= bvSort)

def testSortSubtyping():
    solver = pycvc5.Solver()
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

