###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew Reynolds, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def test_is_null(tm, solver):
    solver.setOption("sygus", "true")
    boolean = tm.getBooleanSort()
    start = tm.mkVar(boolean)
    nts = tm.mkVar(boolean)
    g = solver.mkGrammar([nts], [start])
    assert not g.isNull()


def test_to_string(tm, solver):
    solver.setOption("sygus", "true")
    boolean = tm.getBooleanSort()
    start = tm.mkVar(boolean)
    nts = tm.mkVar(boolean)
    g = solver.mkGrammar([nts], [start])
    g.addRule(start, tm.mkBoolean(False))
    str(g)


def test_add_rule(tm, solver):
    solver.setOption("sygus", "true")
    boolean = tm.getBooleanSort()
    integer = tm.getIntegerSort()

    start = tm.mkVar(boolean)
    nts = tm.mkVar(boolean)

    # expecting no error
    g = solver.mkGrammar([], [start])

    g.addRule(start, tm.mkBoolean(False))

    # expecting errors
    with pytest.raises(RuntimeError):
        g.addRule(nts, tm.mkBoolean(False))
    with pytest.raises(RuntimeError):
        g.addRule(start, tm.mkInteger(0))

    # expecting no errors
    solver.synthFun("f", {}, boolean, g)

    # expecting an error
    with pytest.raises(RuntimeError):
        g.addRule(start, tm.mkBoolean(False))


def test_add_rules(tm, solver):
    solver.setOption("sygus", "true")
    boolean = tm.getBooleanSort()
    integer = tm.getIntegerSort()

    start = tm.mkVar(boolean)
    nts = tm.mkVar(boolean)

    g = solver.mkGrammar([], [start])

    g.addRules(start, {tm.mkBoolean(False)})

    #Expecting errors
    with pytest.raises(RuntimeError):
        g.addRules(nts, [tm.mkBoolean(False)])
    with pytest.raises(RuntimeError):
        g.addRules(start, [tm.mkInteger(0)])

    #Expecting no errors
    solver.synthFun("f", {}, boolean, g)

    #Expecting an error
    with pytest.raises(RuntimeError):
        g.addRules(start, tm.mkBoolean(False))


def test_add_any_constant(tm, solver):
    solver.setOption("sygus", "true")
    boolean = tm.getBooleanSort()

    start = tm.mkVar(boolean)
    nts = tm.mkVar(boolean)

    g = solver.mkGrammar({}, {start})

    g.addAnyConstant(start)
    g.addAnyConstant(start)

    with pytest.raises(RuntimeError):
        g.addAnyConstant(nts)

    solver.synthFun("f", {}, boolean, g)

    with pytest.raises(RuntimeError):
        g.addAnyConstant(start)


def test_add_any_variable(tm, solver):
    solver.setOption("sygus", "true")
    boolean = tm.getBooleanSort()

    x = tm.mkVar(boolean)
    start = tm.mkVar(boolean)
    nts = tm.mkVar(boolean)

    g1 = solver.mkGrammar({x}, {start})
    g2 = solver.mkGrammar({}, {start})

    g1.addAnyVariable(start)
    g1.addAnyVariable(start)
    g2.addAnyVariable(start)

    with pytest.raises(RuntimeError):
        g1.addAnyVariable(nts)

    solver.synthFun("f", {}, boolean, g1)

    with pytest.raises(RuntimeError):
        g1.addAnyVariable(start)

def tesT_hash(tm, solver):
    solver.setOption("sygus", "true")
    bool_sort = tm.getBooleanSort()
    x = tm.mkVar(bool_sort, "x")
    start1 = tm.mkVar(bool_sort, "start")
    start2 = tm.mkVar(bool_sort, "start")

    g1 = solver.mkGrammar({}, {start1})
    g2 = solver.mkGrammar({}, {start1})
    assert hash(g1) == hash(g1)
    assert hash(g1) == hash(g2)

    g1 = solver.mkGrammar({}, {start1})
    g2 = solver.mkGrammar({x}, {start1})
    assert hash(g1) != hash(g2)

    g1 = solver.mkGrammar({x}, {start1})
    g2 = solver.mkGrammar({x}, {start2})
    assert hash(g1) == hash(g2)

    g1 = solver.mkGrammar({x}, {start1})
    g2 = solver.mkGrammar({x}, {start1})
    g2.addAnyVariable(start1)
    assert hash(g1) != hash(g2)

    g1 = solver.mkGrammar({x}, {start1})
    g2 = solver.mkGrammar({x}, {start1})
    g1.addRules(start1, tm.mkFalse())
    g2.addRules(start1, tm.mkFalse())
    assert hash(g1) == hash(g2)

    g1 = solver.mkGrammar({x}, {start1})
    g2 = solver.mkGrammar({x}, {start1})
    g2.addRules(start1, tm.mkFalse())
    assert hash(g1) != hash(g2)

    g1 = solver.mkGrammar({x}, {start1})
    g2 = solver.mkGrammar({x}, {start1})
    g1.addRules(start1, tm.mkTrue())
    g2.addRules(start1, tm.mkFalse())
    assert hash(g1) != hash(g2)
