###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Black-box tests for the SyGuS weight API.
##

import pytest

import cvc5
from cvc5 import Kind


@pytest.fixture
def tm():
    return cvc5.TermManager()


@pytest.fixture
def solver(tm):
    s = cvc5.Solver(tm)
    s.setOption("sygus", "true")
    s.setLogic("NIA")
    return s


def test_declare_weight(solver):
    w = solver.declareWeight("w")
    assert w.getName() == "w"


def test_declare_weight_with_default(tm, solver):
    w = solver.declareWeight("w", tm.mkInteger(5))
    assert w.getName() == "w"
    # The default weight must be an integer value.
    with pytest.raises(RuntimeError):
        solver.declareWeight("bad", tm.mkBoolean(True))


def test_get_default_value(tm, solver):
    five = tm.mkInteger(5)
    w_default = solver.declareWeight("a", five)
    assert w_default.getDefaultValue() == five
    # Weights declared without :default get 0.
    w_zero = solver.declareWeight("b")
    assert w_zero.getDefaultValue() == tm.mkInteger(0)


def test_declare_weight_requires_sygus(tm):
    s = cvc5.Solver(tm)
    with pytest.raises(RuntimeError):
        s.declareWeight("w")


def test_weight_equality(solver):
    w1 = solver.declareWeight("a")
    w2 = solver.declareWeight("b")
    assert w1 == w1
    assert w1 != w2
    assert hash(w1) == hash(w1)


def test_mk_weight_symbol(tm, solver):
    integer = tm.getIntegerSort()
    x = tm.mkVar(integer, "x")
    start = tm.mkVar(integer, "Start")
    w = solver.declareWeight("w")
    g = solver.mkGrammar([x], [start])
    g.addRule(start, x)
    f = solver.synthFun("f", [x], integer, g)
    ws = solver.mkWeightSymbol(w, f)
    assert ws.getSort() == integer

    # mkWeightSymbol requires sygus mode.
    s2 = cvc5.Solver(tm)
    with pytest.raises(RuntimeError):
        s2.mkWeightSymbol(w, f)


def test_grammar_add_rule_with_weights(tm, solver):
    integer = tm.getIntegerSort()
    x = tm.mkVar(integer, "x")
    start = tm.mkVar(integer, "Start")
    w = solver.declareWeight("w")

    g = solver.mkGrammar([x], [start])
    add = tm.mkTerm(Kind.ADD, start, start)
    g.addRule(start, add, {w: tm.mkInteger(1)})

    # Rule must have matching sort.
    with pytest.raises(RuntimeError):
        g.addRule(start, tm.mkBoolean(True), {w: tm.mkInteger(1)})

    # After grammar is bound to synth-fun, addition is rejected.
    solver.synthFun("f", [x], integer, g)
    with pytest.raises(RuntimeError):
        g.addRule(start, x, {w: tm.mkInteger(0)})
