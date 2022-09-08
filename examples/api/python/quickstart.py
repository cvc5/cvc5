#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the api capabilities of cvc5, adapted from quickstart.cpp
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
  # Create a solver
  #! [docs-python-quickstart-1 start]
  solver = cvc5.Solver()
  #! [docs-python-quickstart-1 end]

  # We will ask the solver to produce models and unsat cores,
  # hence these options should be turned on.
  #! [docs-python-quickstart-2 start]
  solver.setOption("produce-models", "true")
  solver.setOption("produce-unsat-cores", "true")
  #! [docs-python-quickstart-2 end]

  # The simplest way to set a logic for the solver is to choose "ALL".
  # This enables all logics in the solver.
  # Alternatively, "QF_ALL" enables all logics without quantifiers.
  # To optimize the solver's behavior for a more specific logic,
  # use the logic name, e.g. "QF_BV" or "QF_AUFBV".

  # Set the logic
  #! [docs-python-quickstart-3 start]
  solver.setLogic("ALL")
  #! [docs-python-quickstart-3 end]

  # In this example, we will define constraints over reals and integers.
  # Hence, we first obtain the corresponding sorts.
  #! [docs-python-quickstart-4 start]
  realSort = solver.getRealSort()
  intSort = solver.getIntegerSort()
  #! [docs-python-quickstart-4 end]

  # x and y will be real variables, while a and b will be integer variables.
  # Formally, their python type is Term,
  # and they are called "constants" in SMT jargon:
  #! [docs-python-quickstart-5 start]
  x = solver.mkConst(realSort, "x")
  y = solver.mkConst(realSort, "y")
  a = solver.mkConst(intSort, "a")
  b = solver.mkConst(intSort, "b")
  #! [docs-python-quickstart-5 end]

  # Our constraints regarding x and y will be:
  #
  #   (1)  0 < x
  #   (2)  0 < y
  #   (3)  x + y < 1
  #   (4)  x <= y
  #

  #! [docs-python-quickstart-6 start]
  # Formally, constraints are also terms. Their sort is Boolean.
  # We will construct these constraints gradually,
  # by defining each of their components.
  # We start with the constant numerals 0 and 1:
  zero = solver.mkReal(0)
  one = solver.mkReal(1)

  # Next, we construct the term x + y
  xPlusY = solver.mkTerm(Kind.ADD, x, y)

  # Now we can define the constraints.
  # They use the operators +, <=, and <.
  # In the API, these are denoted by Plus, Leq, and Lt.
  constraint1 = solver.mkTerm(Kind.LT, zero, x)
  constraint2 = solver.mkTerm(Kind.LT, zero, y)
  constraint3 = solver.mkTerm(Kind.LT, xPlusY, one)
  constraint4 = solver.mkTerm(Kind.LEQ, x, y)

  # Now we assert the constraints to the solver.
  solver.assertFormula(constraint1)
  solver.assertFormula(constraint2)
  solver.assertFormula(constraint3)
  solver.assertFormula(constraint4)
  #! [docs-python-quickstart-6 end]

  # Check if the formula is satisfiable, that is,
  # are there real values for x and y that satisfy all the constraints?
  #! [docs-python-quickstart-7 start]
  r1 = solver.checkSat()
  #! [docs-python-quickstart-7 end]

  # The result is either SAT, UNSAT, or UNKNOWN.
  # In this case, it is SAT.
  #! [docs-python-quickstart-8 start]
  print("expected: sat")
  print("result: ", r1)
  #! [docs-python-quickstart-8 end]

  # We can get the values for x and y that satisfy the constraints.
  #! [docs-python-quickstart-9 start]
  xVal = solver.getValue(x)
  yVal = solver.getValue(y)
  #! [docs-python-quickstart-9 end]

  # It is also possible to get values for compound terms,
  # even if those did not appear in the original formula.
  #! [docs-python-quickstart-10 start]
  xMinusY = solver.mkTerm(Kind.SUB, x, y)
  xMinusYVal = solver.getValue(xMinusY)
  #! [docs-python-quickstart-10 end]

  # We can now obtain the values as python values
  #! [docs-python-quickstart-11 start]
  xPy = xVal.getRealValue()
  yPy = yVal.getRealValue()
  xMinusYPy = xMinusYVal.getRealValue()

  print("value for x: ", xPy)
  print("value for y: ", yPy)
  print("value for x - y: ", xMinusYPy)
  #! [docs-python-quickstart-11 end]

  # Another way to independently compute the value of x - y would be
  # to use the python minus operator instead of asking the solver.
  # However, for more complex terms,
  # it is easier to let the solver do the evaluation.
  #! [docs-python-quickstart-12 start]
  xMinusYComputed = xPy - yPy
  if xMinusYComputed == xMinusYPy:
    print("computed correctly")
  else:
    print("computed incorrectly")
  #! [docs-python-quickstart-12 end]

  # Further, we can convert the values to strings
  #! [docs-python-quickstart-13 start]
  xStr = str(xPy)
  yStr = str(yPy)
  xMinusYStr = str(xMinusYPy)
  #! [docs-python-quickstart-13 end]

  # Next, we will check satisfiability of the same formula,
  # only this time over integer variables a and b.

  # We start by resetting assertions added to the solver.
  #! [docs-python-quickstart-14 start]
  solver.resetAssertions()
  #! [docs-python-quickstart-14 end]

  # Next, we assert the same assertions above with integers.
  # This time, we inline the construction of terms
  # to the assertion command.
  #! [docs-python-quickstart-15 start]
  solver.assertFormula(solver.mkTerm(Kind.LT, solver.mkInteger(0), a))
  solver.assertFormula(solver.mkTerm(Kind.LT, solver.mkInteger(0), b))
  solver.assertFormula(
      solver.mkTerm(
          Kind.LT, solver.mkTerm(Kind.ADD, a, b), solver.mkInteger(1)))
  solver.assertFormula(solver.mkTerm(Kind.LEQ, a, b))
  #! [docs-python-quickstart-15 end]

  # We check whether the revised assertion is satisfiable.
  #! [docs-python-quickstart-16 start]
  r2 = solver.checkSat()
  #! [docs-python-quickstart-16 end]

  # This time the formula is unsatisfiable
  #! [docs-python-quickstart-17 start]
  print("expected: unsat")
  print("result:", r2)
  #! [docs-python-quickstart-17 end]

  # We can query the solver for an unsatisfiable core, i.e., a subset
  # of the assertions that is already unsatisfiable.
  #! [docs-python-quickstart-18 start]
  unsatCore = solver.getUnsatCore()
  print("unsat core size:", len(unsatCore))
  print("unsat core:", unsatCore)
  #! [docs-python-quickstart-18 end]
