###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Aina Niemetz, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for synth result API.
#
# Obtained by translating test/unit/api/synth_result_black.cpp
##

import pytest
import cvc5
from cvc5 import SynthResult


@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def test_is_null(solver):
    res_null = SynthResult()
    assert res_null.isNull()
    assert not res_null.hasSolution()
    assert not res_null.hasNoSolution()
    assert not res_null.isUnknown()


def test_equal(tm, solver):
    solver.setOption("sygus", "true")
    solver.synthFun("f", {}, tm.getBooleanSort())
    tfalse = tm.mkFalse()
    ttrue = tm.mkTrue()
    solver.addSygusConstraint(ttrue)
    res1 = solver.checkSynth()
    solver.addSygusConstraint(tfalse)
    res2 = solver.checkSynth()
    assert res1 == res1
    assert res1 != res2
    assert res1 != SynthResult()


def test_has_solution(tm, solver):
    solver.setOption("sygus", "true")
    f = solver.synthFun("f", [], solver.getBooleanSort())
    boolTerm = tm.mkBoolean(True)
    solver.addSygusConstraint(boolTerm)
    res = solver.checkSynth()
    assert not res.isNull()
    assert res.hasSolution()
    assert not res.hasNoSolution()
    assert not res.isUnknown()
    assert str(res) == '(SOLUTION)'


def test_has_no_solution(solver):
    res_null = SynthResult()
    assert not res_null.hasNoSolution()


def test_has_is_unknown(tm, solver):
    solver.setOption("sygus", "true")
    f = solver.synthFun("f", [], solver.getBooleanSort())
    boolTerm = tm.mkBoolean(False)
    solver.addSygusConstraint(boolTerm)
    res = solver.checkSynth()
    assert not res.isNull()
    assert not res.hasSolution()
    assert res.hasNoSolution()
    assert not res.isUnknown()
