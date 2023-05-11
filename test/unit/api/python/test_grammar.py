###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew Reynolds, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Translated from test/unit/api/grammar_black.h
##

import pytest

import cvc5
from cvc5 import Term


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_to_string(solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)
    g = solver.mkGrammar([nts], [start])
    g.addRule(start, solver.mkBoolean(False))
    str(g)


def test_add_rule(solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()
    integer = solver.getIntegerSort()

    null_term = Term(solver)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    # expecting no error
    g = solver.mkGrammar([], [start])

    g.addRule(start, solver.mkBoolean(False))

    # expecting errors
    with pytest.raises(RuntimeError):
        g.addRule(null_term, solver.mkBoolean(False))
    with pytest.raises(RuntimeError):
        g.addRule(start, null_term)
    with pytest.raises(RuntimeError):
        g.addRule(nts, solver.mkBoolean(False))
    with pytest.raises(RuntimeError):
        g.addRule(start, solver.mkInteger(0))
    with pytest.raises(RuntimeError):
        g.addRule(start, nts)

    # expecting no errors
    solver.synthFun("f", {}, boolean, g)

    # expecting an error
    with pytest.raises(RuntimeError):
        g.addRule(start, solver.mkBoolean(False))


def test_add_rules(solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()
    integer = solver.getIntegerSort()

    null_term = Term(solver)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    g = solver.mkGrammar([], [start])

    g.addRules(start, {solver.mkBoolean(False)})

    #Expecting errors
    with pytest.raises(RuntimeError):
        g.addRules(null_term, [solver.mkBoolean(False)])
    with pytest.raises(RuntimeError):
        g.addRules(start, [null_term])
    with pytest.raises(RuntimeError):
        g.addRules(nts, [solver.mkBoolean(False)])
    with pytest.raises(RuntimeError):
        g.addRules(start, [solver.mkInteger(0)])
    with pytest.raises(RuntimeError):
        g.addRules(start, [nts])
    #Expecting no errors
    solver.synthFun("f", {}, boolean, g)

    #Expecting an error
    with pytest.raises(RuntimeError):
        g.addRules(start, solver.mkBoolean(False))


def test_add_any_constant(solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()

    null_term = Term(solver)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    g = solver.mkGrammar({}, {start})

    g.addAnyConstant(start)
    g.addAnyConstant(start)

    with pytest.raises(RuntimeError):
        g.addAnyConstant(null_term)
    with pytest.raises(RuntimeError):
        g.addAnyConstant(nts)

    solver.synthFun("f", {}, boolean, g)

    with pytest.raises(RuntimeError):
        g.addAnyConstant(start)


def test_add_any_variable(solver):
    solver.setOption("sygus", "true")
    boolean = solver.getBooleanSort()

    null_term = Term(solver)
    x = solver.mkVar(boolean)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    g1 = solver.mkGrammar({x}, {start})
    g2 = solver.mkGrammar({}, {start})

    g1.addAnyVariable(start)
    g1.addAnyVariable(start)
    g2.addAnyVariable(start)

    with pytest.raises(RuntimeError):
        g1.addAnyVariable(null_term)
    with pytest.raises(RuntimeError):
        g1.addAnyVariable(nts)

    solver.synthFun("f", {}, boolean, g1)

    with pytest.raises(RuntimeError):
        g1.addAnyVariable(start)
