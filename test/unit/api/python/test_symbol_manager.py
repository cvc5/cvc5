###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5

from cvc5 import InputParser, SymbolManager

@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)

def test_constructor(tm, solver):
    SymbolManager(tm)
    SymbolManager(solver) # deprecated

def parse_command(solver, sm, cmd):
    parser = InputParser(solver, sm)
    parser.setIncrementalStringInput(
            cvc5.InputLanguage.SMT_LIB_2_6, "test_symbol_manager_parser")
    parser.appendIncrementalStringInput(cmd)
    cmd = parser.nextCommand()
    assert cmd.isNull() is not True
    cmd.invoke(solver, sm)
    
def parse_and_set_logic(solver, sm, logic):
    parse_command(solver, sm, "(set-logic " + logic + ")" + '\n')

def test_is_logic_set(tm, solver):
    sm = SymbolManager(tm)
    assert sm.isLogicSet() is False
    parse_and_set_logic(solver, sm, "QF_LIA")
    assert sm.isLogicSet() is True

def test_get_logic(tm, solver):
    sm = SymbolManager(tm)
    with pytest.raises(RuntimeError):
        sm.getLogic()
    parse_and_set_logic(solver, sm, "QF_LIA")
    assert sm.getLogic() == "QF_LIA"

def test_get_declared_terms_and_sorts(tm, solver):
    sm = SymbolManager(tm)
    assert len(sm.getDeclaredSorts()) == 0
    assert len(sm.getDeclaredTerms()) == 0

def test_get_named_terms(tm, solver):
    sm = SymbolManager(tm)
    parse_and_set_logic(solver, sm, "QF_LIA")
    assert len(sm.getNamedTerms()) == 0
    parse_command(solver, sm, "(assert (! false :named a0))")
    assert len(sm.getNamedTerms()) == 1

