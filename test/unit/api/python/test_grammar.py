# translated from test/unit/api/grammar_black.h

import pytest

import pycvc4
from pycvc4 import kinds

def test_add_rule():
  solver = pycvc4.Solver()
  boolean = solver.getBooleanSort()
  integer = solver.getIntegerSort()

  nullTerm = pycvc4.Term(solver)
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  # expecting no error
  g = solver.mkSygusGrammar([], [start])

  g.addRule(start, solver.mkBoolean(False))

  # expecting errors
  with pytest.raises(Exception):
    g.addRule(nullTerm, solver.mkBoolean(false))
  with pytest.raises(Exception):
    g.addRule(start, nullTerm)
  with pytest.raises(Exception):
    g.addRule(nts, solver.mkBoolean(false))
  with pytest.raises(Exception):
    g.addRule(start, solver.mkReal(0))

  # expecting no errors
  solver.synthFun("f", {}, boolean, g)

  # expecting an error
  with pytest.raises(Exception):
    g.addRule(start, solver.mkBoolean(false))

def test_add_rules():
  solver = pycvc4.Solver()
  boolean = solver.getBooleanSort()
  integer = solver.getIntegerSort()

  nullTerm = pycvc4.Term(solver)
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  g = solver.mkSygusGrammar([], [start])

  g.addRules(start, {solver.mkBoolean(False)})

  #Expecting errors
  with pytest.raises(Exception):
    g.addRules(nullTerm, solver.mkBoolean(False))
  with pytest.raises(Exception):
    g.addRules(start, {nullTerm})
  with pytest.raises(Exception):
    g.addRules(nts, {solver.mkBoolean(False)})
  with pytest.raises(Exception):
    g.addRules(start, {solver.mkReal(0)})
  #Expecting no errors
  solver.synthFun("f", {}, boolean, g)

  #Expecting an error
  with pytest.raises(Exception):
    g.addRules(start, solver.mkBoolean(False))

def testAddAnyConstant():
  solver = pycvc4.Solver()
  boolean = solver.getBooleanSort()

  nullTerm = pycvc4.Term(solver)
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  g = solver.mkSygusGrammar({}, {start})

  g.addAnyConstant(start)
  g.addAnyConstant(start)

  with pytest.raises(Exception):
    g.addAnyConstant(nullTerm)
  with pytest.raises(Exception):
    g.addAnyConstant(nts)

  solver.synthFun("f", {}, boolean, g)

  with pytest.raises(Exception):
    g.addAnyConstant(start)


def testAddAnyVariable():
  solver = pycvc4.Solver()
  boolean = solver.getBooleanSort()

  nullTerm = pycvc4.Term(solver)
  x = solver.mkVar(boolean)
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  g1 = solver.mkSygusGrammar({x}, {start})
  g2 = solver.mkSygusGrammar({}, {start})

  g1.addAnyVariable(start)
  g1.addAnyVariable(start)
  g2.addAnyVariable(start)

  with pytest.raises(Exception):
    g1.addAnyVariable(nullTerm)
  with pytest.raises(Exception):
    g1.addAnyVariable(nts)

  solver.synthFun("f", {}, boolean, g1)

  with pytest.raises(Exception):
    g1.addAnyVariable(start)

