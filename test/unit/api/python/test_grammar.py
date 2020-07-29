import pytest

import pycvc4
from pycvc4 import kinds

def test_add_rule():
  solver = pycvc4.Solver()
  boolean = solver.getBooleanSort()
  integer = solver.getIntegerSort()

  nullTerm = Term()
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)
  
  # expecting no error
  g = solver.mkSygusGrammar(start, nts)

  g.addRule(start, solver.mkBoolean(false))

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

  boolean = solver.getBooleanSort()
  integer = solver.getIntegerSort()

  nullTerm = Term()
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  g = solver.mkSygusGrammar({}, start)

  g.addRules(start, solver.mkBoolean(false))

  with pytest.raises(Exception):
    g.addRules(nullTerm, solver.mkBoolean(false))
  with pytest.raises(Exception):
    g.addRules(start, nullTerm)
  with pytest.raises(Exception):
    g.addRules(nts, solver.mkBoolean(false))
  with pytest.raises(Exception):
    g.addRules(start, solver.mkReal(0))
  solver.synthFun("f", {}, boolean, g)
  with pytest.raises(Exception):
    g.addRules(start, solver.mkBoolean(false))

def testAddAnyConstant():

  boolean = solver.getBooleanSort()

  nullTerm = Term()
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  g = solver.mkSygusGrammar({}, start)

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
  boolean = solver.getBooleanSort()

  nullTerm = Term()
  x = solver.mkVar(boolean)
  start = solver.mkVar(boolean)
  nts = solver.mkVar(boolean)

  g1 = solver.mkSygusGrammar({x}, start)
  g2 = solver.mkSygusGrammar({}, start)

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

