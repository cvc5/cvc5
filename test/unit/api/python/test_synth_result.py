###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
def solver():
    return cvc5.Solver()


def test_is_null(solver):
    res_null = SynthResult(solver)
    assert res_null.isNull()
    assert not res_null.hasSolution()
    assert not res_null.hasNoSolution()
    assert not res_null.isUnknown()

def test_has_solution(solver):
    solver.setOption("sygus", "true")
    f = solver.synthFun("f", [], solver.getBooleanSort())
    boolTerm = solver.mkBoolean(True)
    solver.addSygusConstraint(boolTerm)
    res = solver.checkSynth()
    assert not res.isNull()
    assert res.hasSolution()
    assert not res.hasNoSolution()
    assert not res.isUnknown()
    assert str(res) == '(SOLUTION)'

def test_has_no_solution(solver):
    res_null = SynthResult(solver)
    assert not res_null.hasNoSolution()

def test_has_is_unknown(solver):
    solver.setOption("sygus", "true")
    f = solver.synthFun("f", [], solver.getBooleanSort())
    boolTerm = solver.mkBoolean(False)
    solver.addSygusConstraint(boolTerm)
    res = solver.checkSynth()
    assert not res.isNull()
    assert not res.hasSolution()
    assert res.hasNoSolution()
    assert not res.isUnknown()
