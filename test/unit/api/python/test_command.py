###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

def parse_command(solver, sm, cmd_str):
    parser = InputParser(solver, sm)
    parser.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_command")
    parser.appendIncrementalStringInput(cmd_str + '\n')
    return parser.nextCommand()


def test_invoke(tm, solver):
    sm = SymbolManager(tm)
    cmd = parse_command(solver, sm, "(set-logic QF_LIA)")
    assert cmd.isNull() is not True
    cmd.invoke(solver, sm)
    # get model not available
    cmd = parse_command(solver, sm, "(get-model)")
    assert cmd.isNull() is not True
    cmd.invoke(solver, sm)
    # logic already set
    with pytest.raises(RuntimeError):
        parse_command(solver, sm, "(set-logic QF_LRA)")

def test_to_string(tm, solver):
    sm = SymbolManager(tm)
    cmd = parse_command(solver, sm, "(set-logic QF_LIA )")
    assert cmd.isNull() is not True
    # note normalizes wrt whitespace
    assert cmd.toString() == "(set-logic QF_LIA)"

def test_get_command_name(tm, solver):
    sm = SymbolManager(tm)
    cmd = parse_command(solver, sm, "(get-model)")
    assert cmd.isNull() is not True
    assert cmd.getCommandName() == "get-model"
