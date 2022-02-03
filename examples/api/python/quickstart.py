#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
  solver = cvc5.Solver()

  # We will ask the solver to produce models and unsat cores,
  # hence these options should be turned on.
  solver.setOption("produce-models", "true");
  solver.setOption("produce-unsat-cores", "true");

  # The simplest way to set a logic for the solver is to choose "ALL".
  # This enables all logics in the solver.
  # Alternatively, "QF_ALL" enables all logics without quantifiers.
  # To optimize the solver's behavior for a more specific logic,
  # use the logic name, e.g. "QF_BV" or "QF_AUFBV".

  # Set the logic
  solver.setLogic("ALL");

  # In this example, we will define constraints over reals and integers.
  # Hence, we first obtain the corresponding sorts.
  realSort = solver.getRealSort();
  intSort = solver.getIntegerSort();

  # x and y will be real variables, while a and b will be integer variables.
  # Formally, their python type is Term,
  # and they are called "constants" in SMT jargon:
  x = solver.mkConst(realSort, "x");
  y = solver.mkConst(realSort, "y");
  a = solver.mkConst(intSort, "a");
  b = solver.mkConst(intSort, "b");

  # Our constraints regarding x and y will be:
  #
  #   (1)  0 < x
  #   (2)  0 < y
  #   (3)  x + y < 1
  #   (4)  x <= y
  #

  # Formally, constraints are also terms. Their sort is Boolean.
  # We will construct these constraints gradually,
  # by defining each of their components.
  # We start with the constant numerals 0 and 1:
  zero = solver.mkReal(0);
  one = solver.mkReal(1);

  # Next, we construct the term x + y
  xPlusY = solver.mkTerm(Kind.Add, x, y);

  # Now we can define the constraints.
  # They use the operators +, <=, and <.
  # In the API, these are denoted by Plus, Leq, and Lt.
  constraint1 = solver.mkTerm(Kind.Lt, zero, x);
  constraint2 = solver.mkTerm(Kind.Lt, zero, y);
  constraint3 = solver.mkTerm(Kind.Lt, xPlusY, one);
  constraint4 = solver.mkTerm(Kind.Leq, x, y);

  # Now we assert the constraints to the solver.
  solver.assertFormula(constraint1);
  solver.assertFormula(constraint2);
  solver.assertFormula(constraint3);
  solver.assertFormula(constraint4);

  # Check if the formula is satisfiable, that is,
  # are there real values for x and y that satisfy all the constraints?
  r1 = solver.checkSat();

  # The result is either SAT, UNSAT, or UNKNOWN.
  # In this case, it is SAT.
  print("expected: sat")
  print("result: ", r1)

  # We can get the values for x and y that satisfy the constraints.
  xVal = solver.getValue(x);
  yVal = solver.getValue(y);

  # It is also possible to get values for compound terms,
  # even if those did not appear in the original formula.
  xMinusY = solver.mkTerm(Kind.Sub, x, y);
  xMinusYVal = solver.getValue(xMinusY);
  
  # We can now obtain the values as python values
  xPy = xVal.getRealValue();
  yPy = yVal.getRealValue();
  xMinusYPy = xMinusYVal.getRealValue();

  print("value for x: ", xPy)
  print("value for y: ", yPy)
  print("value for x - y: ", xMinusYPy)

  # Another way to independently compute the value of x - y would be
  # to use the python minus operator instead of asking the solver.
  # However, for more complex terms,
  # it is easier to let the solver do the evaluation.
  xMinusYComputed = xPy - yPy;
  if xMinusYComputed == xMinusYPy:
    print("computed correctly") 
  else:
    print("computed incorrectly")

  # Further, we can convert the values to strings
  xStr = str(xPy);
  yStr = str(yPy);
  xMinusYStr = str(xMinusYPy);


  # Next, we will check satisfiability of the same formula,
  # only this time over integer variables a and b.

  # We start by resetting assertions added to the solver.
  solver.resetAssertions();

  # Next, we assert the same assertions above with integers.
  # This time, we inline the construction of terms
  # to the assertion command.
  solver.assertFormula(solver.mkTerm(Kind.Lt, solver.mkInteger(0), a));
  solver.assertFormula(solver.mkTerm(Kind.Lt, solver.mkInteger(0), b));
  solver.assertFormula(
      solver.mkTerm(Kind.Lt, solver.mkTerm(Kind.Add, a, b), solver.mkInteger(1)));
  solver.assertFormula(solver.mkTerm(Kind.Leq, a, b));

  # We check whether the revised assertion is satisfiable.
  r2 = solver.checkSat();

  # This time the formula is unsatisfiable
  print("expected: unsat")
  print("result:", r2)

  # We can query the solver for an unsatisfiable core, i.e., a subset
  # of the assertions that is already unsatisfiable.
  unsatCore = solver.getUnsatCore();
  print("unsat core size:", len(unsatCore))
  print("unsat core:", unsatCore)
