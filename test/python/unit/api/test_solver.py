#####################
## test_solver.py
## Top contributors (to current version):
##   Yoni Zohar, Ying Sheng
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
import pytest
import pycvc4
import sys

from pycvc4 import kinds
from contextlib import contextmanager

@pytest.fixture
def solver():
    return pycvc4.Solver()

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

def 
