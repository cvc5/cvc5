###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5

from cvc5 import InputParser, SymbolManager, stringstream, endl

@pytest.fixture
def solver():
    return cvc5.Solver()

def parse_and_set_logic(solver, sm, logic):
    ss = stringstream()
    ss << "(set-logic " << logic << ")" << endl
    parser = InputParser(solver, sm)
    parser.setStreamInput(cvc5.InputLanguage.SMT_LIB_2_6, ss, "test_input_parser")
    cmd = parser.nextCommand()
    assert cmd.isNull() is not True
    out = stringstream()
    cmd.invoke(solver, sm, out)

def test_is_logic_set(solver):
    sm = SymbolManager(solver)
    assert sm.isLogicSet() is False
    parse_and_set_logic(solver, sm, "QF_LIA")
    assert sm.isLogicSet() is True

def test_get_logic(solver):
    sm = SymbolManager(solver)
    with pytest.raises(RuntimeError):
        sm.getLogic()
    parse_and_set_logic(solver, sm, "QF_LIA")
    assert sm.getLogic() == "QF_LIA"
