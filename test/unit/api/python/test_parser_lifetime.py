###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Lifetime tests for the Python parser API.
#
# A symbol manager keeps the internal node manager alive (it holds its own
# copy of the term manager). Terms and sorts obtained through the parser must
# therefore remain usable after the parser, symbol manager, solver and term
# manager that produced them are dropped. CPython's deterministic reference
# counting (``del`` + ``gc.collect()``) lets us trigger this precisely.
#
# Note: the Python wrappers also hold a reference to the TermManager, so these
# tests primarily exercise that binding-level keepalive; the underlying native
# shared_ptr guarantee is proven by the C++ and Java suites.
#
# Mirrors test/unit/api/cpp/api_parser_lifetime_black.cpp.
##

import gc
import pytest
import cvc5

from cvc5 import Kind, TermManager, Solver, SymbolManager, InputParser


def test_symbol_manager_outlives_term_manager():
    tm = TermManager()
    sm = SymbolManager(tm)
    del tm
    gc.collect()
    assert sm.isLogicSet() is False
    assert len(sm.getDeclaredTerms()) == 0
    assert len(sm.getDeclaredSorts()) == 0


def test_declared_symbols_outlive_parser_and_managers():
    tm = TermManager()
    solver = Solver(tm)
    sm = SymbolManager(tm)
    p = InputParser(solver, sm)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6,
                                "parser_lifetime")
    p.appendIncrementalStringInput("(set-logic ALL)\n")
    p.appendIncrementalStringInput("(declare-sort U 0)\n")
    p.appendIncrementalStringInput("(declare-fun a () Int)\n")
    p.appendIncrementalStringInput("(declare-fun b () U)\n")
    cmd = p.nextCommand()
    while not cmd.isNull():
        cmd.invoke(solver, sm)
        cmd = p.nextCommand()
    terms = sm.getDeclaredTerms()
    sorts = sm.getDeclaredSorts()
    assert len(terms) == 2
    assert len(sorts) == 1
    del p
    del sm
    del solver
    del tm
    gc.collect()
    for t in terms:
        assert not t.isNull()
        t.getSort()
        assert str(t)
    for s in sorts:
        assert not s.isNull()
        assert str(s)


def test_parsed_term_outlives_parser_and_managers():
    tm = TermManager()
    solver = Solver(tm)
    sm = SymbolManager(tm)
    p = InputParser(solver, sm)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6,
                                "parser_lifetime")
    p.appendIncrementalStringInput("(set-logic ALL)\n")
    p.appendIncrementalStringInput("(declare-fun x () Int)\n")
    cmd = p.nextCommand()
    cmd.invoke(solver, sm)
    cmd = p.nextCommand()
    cmd.invoke(solver, sm)
    p.appendIncrementalStringInput("(+ x 1)\n")
    t = p.nextTerm()
    del p
    del sm
    del solver
    del tm
    gc.collect()
    assert not t.isNull()
    assert t.getKind() == Kind.ADD
    assert t.getSort().isInteger()
    assert str(t)


def test_parsed_term_outlives_parser_with_internal_symbol_manager():
    tm = TermManager()
    solver = Solver(tm)
    # This parser allocates and owns its own symbol manager.
    p = InputParser(solver)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6,
                                "parser_lifetime")
    p.appendIncrementalStringInput("(set-logic ALL)\n")
    p.appendIncrementalStringInput("(declare-fun x () Int)\n")
    cmd = p.nextCommand()
    cmd.invoke(solver, p.getSymbolManager())
    cmd = p.nextCommand()
    cmd.invoke(solver, p.getSymbolManager())
    p.appendIncrementalStringInput("(* x 2)\n")
    t = p.nextTerm()
    del p
    del solver
    del tm
    gc.collect()
    assert not t.isNull()
    assert t.getKind() == Kind.MULT
    assert t.getSort().isInteger()
    assert str(t)


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__]))
