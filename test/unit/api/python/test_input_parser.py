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

from contextlib import contextmanager
import pytest
import cvc5

from cvc5 import InputParser, SymbolManager

@contextmanager
def does_not_raise():
    yield

@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)

def test_get_solver(solver):
    p = InputParser(solver)
    assert p.getSolver() is solver

def test_symbol_manager(solver):
    p = InputParser(solver)
    assert isinstance(p.getSymbolManager(), SymbolManager)

    sm = SymbolManager(solver)
    p2 = InputParser(solver, sm)
    assert p2.getSymbolManager() is sm

def test_set_file_input(solver):
    p = InputParser(solver)
    with pytest.raises(RuntimeError):
        p.setFileInput(cvc5.InputLanguage.SMT_LIB_2_6, "nonexistent.smt2")

def test_set_and_append_incremental_string_input(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    p.appendIncrementalStringInput("(set-logic ALL)")
    p.appendIncrementalStringInput("(declare-fun a () Bool)")
    p.appendIncrementalStringInput("(declare-fun b () Int)")
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)

def test_set_and_append_incremental_string_input_interleave(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    p.appendIncrementalStringInput("(set-logic ALL)")
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)
    p.appendIncrementalStringInput("(declare-fun a () Bool)")
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)
    p.appendIncrementalStringInput("(declare-fun b () Int)")
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)

def test_append_incremental_no_set(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    with pytest.raises(RuntimeError):
        p.appendIncrementalStringInput("(set-logic ALL)")

def test_set_string_input(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    p.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "(set-logic ALL)", "test_input_parser")
    cmd = p.nextCommand()
    assert cmd.isNull() is False
    with does_not_raise():
        cmd.invoke(solver, sm)
    cmd = p.nextCommand()
    assert cmd.isNull() is True

def test_next_command_no_input(solver):
    p = InputParser(solver)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    cmd = p.nextCommand()
    assert cmd.isNull() is True
    t = p.nextTerm()
    assert cmd.isNull() is True

def test_next_term(solver):
    p = InputParser(solver)
    with pytest.raises(RuntimeError):
        p.nextTerm()
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    assert p.nextTerm().isNull() is True

def test_next_term2(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    # parse a declaration command
    p.appendIncrementalStringInput("(declare-fun a () Int)")
    cmd = p.nextCommand()
    assert cmd.isNull() is not True
    with does_not_raise():
        cmd.invoke(solver, sm)
    # now parse some terms
    t = None
    p.appendIncrementalStringInput("45\n")
    with does_not_raise():
        t = p.nextTerm()
    assert t.isNull() is False
    p.appendIncrementalStringInput("(+ a 1)\n")
    with does_not_raise():
        t = p.nextTerm()
    assert t.isNull() is False
    assert t.getKind() == cvc5.Kind.ADD
    p.appendIncrementalStringInput("(+ b 1)\n")
    with pytest.raises(RuntimeError):
        t = p.nextTerm()

def parse_logic_command(p, logic):
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    p.appendIncrementalStringInput("(set-logic " + logic + ")\n")
    return p.nextCommand()

def test_multiple_parsers(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    # set a logic for the parser
    cmd = parse_logic_command(p, "QF_LIA")
    with does_not_raise():
        cmd.invoke(solver, sm)
    assert solver.isLogicSet() is True
    assert solver.getLogic() == "QF_LIA"
    assert sm.isLogicSet() is True
    assert sm.getLogic() == "QF_LIA"
    # cannot set logic on solver now
    with pytest.raises(RuntimeError):
      solver.setLogic("QF_LRA")
    
    # possible to construct another parser with the same solver and symbol
    # manager
    p2 = InputParser(solver, p.getSymbolManager())

    # possible to construct another parser with a fresh solver
    s2 = cvc5.Solver()
    p3 = InputParser(s2, sm)
    p3.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")

    # logic is automatically set on the solver
    assert s2.isLogicSet() is True
    assert s2.getLogic() == "QF_LIA"
    # we cannot set the logic since it has already been set
    with pytest.raises(RuntimeError):
      parse_logic_command(p3, "QF_LRA")
    assert p3.done() is True

    # using a solver with the same logic is allowed
    s3 = cvc5.Solver()
    s3.setLogic("QF_LIA")
    p4 = InputParser(s3, sm)
    p4.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")

    # using a solver with a different logic is not allowed
    s4 = cvc5.Solver()
    s4.setLogic("QF_LRA")
    p5 = InputParser(s4, sm)
    with pytest.raises(RuntimeError):
        p5.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")


def test_get_declared_terms_and_sorts(solver):
    sm = SymbolManager(solver)
    p = InputParser(solver, sm)
    p.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "test_input_parser")
    p.appendIncrementalStringInput("(set-logic ALL)")
    p.appendIncrementalStringInput("(declare-sort U 0)")
    p.appendIncrementalStringInput("(declare-fun x () U)")
    for i in [0,1,2]:
      cmd = p.nextCommand()
      assert cmd.isNull() != True
      cmd.invoke(solver, sm);
    sorts = sm.getDeclaredSorts();
    terms = sm.getDeclaredTerms();
    assert len(sorts) == 1
    assert len(terms) == 1
    assert terms[0].getSort() == sorts[0]
  
