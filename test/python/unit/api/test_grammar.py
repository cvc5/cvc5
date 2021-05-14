###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Makai Mann, Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Translated from test/unit/api/grammar_black.h
##

import pytest

import pycvc5
from pycvc5 import kinds, Term


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_add_rule(solver):
    boolean = solver.getBooleanSort()
    integer = solver.getIntegerSort()

    null_term = Term(solver)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    # expecting no error
    g = solver.mkSygusGrammar([], [start])

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
    boolean = solver.getBooleanSort()
    integer = solver.getIntegerSort()

    null_term = Term(solver)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    g = solver.mkSygusGrammar([], [start])

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
    boolean = solver.getBooleanSort()

    null_term = Term(solver)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    g = solver.mkSygusGrammar({}, {start})

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
    boolean = solver.getBooleanSort()

    null_term = Term(solver)
    x = solver.mkVar(boolean)
    start = solver.mkVar(boolean)
    nts = solver.mkVar(boolean)

    g1 = solver.mkSygusGrammar({x}, {start})
    g2 = solver.mkSygusGrammar({}, {start})

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
