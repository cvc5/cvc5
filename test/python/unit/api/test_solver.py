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

@contextmanager
def assert_no_raises(ExpectedException):
    try:
        yield

    except ExpectedException as error:
        pytest.fail()
        raise AssertionError(f"Raised exception {error} when it should not!")

    except Exception as error:
        pytest.fail()
        raise AssertionError(f"An unexpected exception {error} raised.")

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
        with assert_no_raises(RuntimeError):
            solver.mkRoundingMode(pycvc4.RoundNearestTiesToEven)
    else:
        with pytest.raises(RuntimeError):
            solver.mkRoundingMode(pycvc4.RoundNearestTiesToEven)

def test_get_boolean_sort(solver):
    with assert_no_raises(RuntimeError):
        solver.getBooleanSort()

def test_get_integer_sort(solver):
    with assert_no_raises(RuntimeError):
        solver.getIntegerSort()

#def test_get_null_sort(solver):
#    try:
#        solver.getNullSort()
#    except RuntimeError:
#        pytest.fail()

def test_get_real_sort(solver):
    with assert_no_raises(RuntimeError):
        solver.getRealSort()

def test_get_reg_exp_sort(solver):
    with assert_no_raises(RuntimeError):
        solver.getRegExpSort()

def test_get_string_sort(solver):
    with assert_no_raises(RuntimeError):
        solver.getStringSort()

def test_get_rounding_mode_sort(solver):
    if solver.supportsFloatingPoint():
        with assert_no_raises(RuntimeError):
            solver.getRoundingModeSort()
    else:
        with pytest.raises(RuntimeError):
            solver.getRoundingModeSort()
