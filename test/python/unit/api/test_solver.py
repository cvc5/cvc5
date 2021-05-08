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
        solver.mkRoundingMode(pycvc4.RoundNearestTiesToEven)
    else:
        with pytest.raises(RuntimeError):
            solver.mkRoundingMode(pycvc4.RoundNearestTiesToEven)

def test_getBooleanSort(solver):
    solver.getBooleanSort()

def test_getIntegerSort(solver):
    solver.getIntegerSort()

#def test_getNullSort(solver):
#        solver.getNullSort()

def test_getRealSort(solver):
    solver.getRealSort()

def test_getRegExpSort(solver):
    solver.getRegExpSort()

def test_getStringSort(solver):
    solver.getStringSort()

def test_get_rounding_mode_sort(solver):
    if solver.supportsFloatingPoint():
        solver.getRoundingModeSort()
    else:
        with pytest.raises(RuntimeError):
            solver.getRoundingModeSort()

def test_mkArraySort(solver):
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

    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkArraySort(boolSort, boolSort)

def test_mkBitVectorSort(solver):
    solver.mkBitVectorSort(32);
    with pytest.raises(RuntimeError):
        solver.mkBitVectorSort(0)

def test_mkFloatingPointSort(solver):
    if solver.supportsFloatingPoint():
        solver.mkFloatingPointSort(4, 8)
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(0, 8)
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(4, 0)
    else:
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(4, 8)

def test_mkDatatypeSort(solver):
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    solver.mkDatatypeSort(dtypeSpec)

    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSort(dtypeSpec)

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSort(throwsDtypeSpec)

def test_mkDatatypeSorts(solver):
    slv = pycvc4.Solver()
    
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

def test_mkFunctionSort(solver):
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
    
    slv = pycvc4.Solver()
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

def test_mkParamSort(solver):
    solver.mkParamSort("T")
    solver.mkParamSort("")

def test_mkPredicateSort(solver):
    solver.mkPredicateSort([solver.getIntegerSort()])
    with pytest.raises(RuntimeError):
        solver.mkPredicateSort([])

    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    # functions as arguments are allowed
    solver.mkPredicateSort([solver.getIntegerSort(), funSort])

    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkPredicateSort([solver.getIntegerSort()])

def test_mkRecordSort(solver):
    fields = [("b", solver.getBooleanSort()),\
              ("bv", solver.mkBitVectorSort(8)),\
              ("i", solver.getIntegerSort())]
    empty = []
    solver.mkRecordSort(fields)
    solver.mkRecordSort(empty)
    recSort = solver.mkRecordSort(fields)
    recSort.getDatatype()

def test_mkSetSort(solver):
    solver.mkSetSort(solver.getBooleanSort())
    solver.mkSetSort(solver.getIntegerSort())
    solver.mkSetSort(solver.mkBitVectorSort(4))
    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSetSort(solver.mkBitVectorSort(4))

#def test_mkBagSort(solver):
#    solver.mkBagSort(solver.getBooleanSort())
#    solver.mkBadSort(solver.getIntegerSort())
#    solver.mkBagSort(solver.mkBitVectorSort(4))
#    slv = pycvc4.Solver()
#    with pytest.raises(RuntimeError):
#        slv.mkBagSort(solver.mkBitVectorSort(4))

def test_mkSequenceSort(solver):
    solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkSequenceSort(\
            solver.mkSequenceSort(solver.getIntegerSort()))
    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSequenceSort(solver.getIntegerSort())

def test_mkUninterpretedSort(solver):
    solver.mkUninterpretedSort("u")
    solver.mkUninterpretedSort("")

def test_mkSortConstructorSort(solver):
    solver.mkSortConstructorSort("s", 2)
    solver.mkSortConstructorSort("", 2)
    with pytest.raises(RuntimeError):
        solver.mkSortConstructorSort("", 0)

def test_mkTupleSort(solver):
    solver.mkTupleSort([solver.getIntegerSort()])
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkTupleSort([solver.getIntegerSort(), funSort])

    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkTupleSort([solver.getIntegerSort()])

def test_mkBitVector(solver):
    size0, size1, size2 = 0, 8, 32
    val1, val2 = 2, 2
    solver.mkBitVector(size1, val1)
    solver.mkBitVector(size2, val2)
    solver.mkBitVector("1010", 2)
    solver.mkBitVector("1010", 10)
    solver.mkBitVector("1234", 10)
    solver.mkBitVector("1010", 16)
    solver.mkBitVector("a09f", 16)
    #solver.mkBitVector(8, "-127", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(size0, val1)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(size0, val2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector("", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector("10", 3)
    with pytest.raises(RuntimeError):
        solver.mkBitVector("20", 2)
#    with pytest.raises(RuntimeError):
#        solver.mkBitVector(8, "101010101", 2)
#    with pytest.raises(RuntimeError):
#        solver.mkBitVector(8, "-256", 10)
    assert solver.mkBitVector("1010", 2) == solver.mkBitVector("10", 10)
    assert solver.mkBitVector("1010", 2) == solver.mkBitVector("a", 16)
#    assert solver.mkBitVector(8, "01010101", 2).toString() == "#b01010101"
#    assert solver.mkBitVector(8, "F", 16).toString() == "#b00001111"
#    assert solver.mkBitVector(8, "-1", 10) ==\
#           solver.mkBitVector(8, "FF", 16)

def test_mkVar(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkVar(boolSort)
    solver.mkVar(funSort)
    solver.mkVar(boolSort, "b")
    solver.mkVar(funSort, "")
#    with pytest.raises(RuntimeError):
#        solver.mkVar(Sort())
#    with pytest.raises(RuntimeError):
#        solver.mkVar(Sort(), "a")
    slv = pycvc4.Solver()
    with pytest.raises(RuntimeError):
        slv.mkVar(boolSort, "x")
