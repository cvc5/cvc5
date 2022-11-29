/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the api capabilities of cvc5.
 *
 */

import io.github.cvc5.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class QuickStart
{
  public static void main(String args[]) throws CVC5ApiException
  {
    // Create a solver
    Solver solver = new Solver();
    {
      // We will ask the solver to produce models and unsat cores,
      // hence these options should be turned on.
      //! [docs-java-quickstart-1 start]
      solver.setOption("produce-models", "true");
      solver.setOption("produce-unsat-cores", "true");
      //! [docs-java-quickstart-1 end]

      // The simplest way to set a logic for the solver is to choose "ALL".
      // This enables all logics in the solver.
      // Alternatively, "QF_ALL" enables all logics without quantifiers.
      // To optimize the solver's behavior for a more specific logic,
      // use the logic name, e.g. "QF_BV" or "QF_AUFBV".

      // Set the logic
      //! [docs-java-quickstart-2 start]
      solver.setLogic("ALL");
      //! [docs-java-quickstart-2 end]

      // In this example, we will define constraints over reals and integers.
      // Hence, we first obtain the corresponding sorts.
      //! [docs-java-quickstart-3 start]
      Sort realSort = solver.getRealSort();
      Sort intSort = solver.getIntegerSort();
      //! [docs-java-quickstart-3 end]

      // x and y will be real variables, while a and b will be integer variables.
      // Formally, their cpp type is Term,
      // and they are called "constants" in SMT jargon:
      //! [docs-java-quickstart-4 start]
      Term x = solver.mkConst(realSort, "x");
      Term y = solver.mkConst(realSort, "y");
      Term a = solver.mkConst(intSort, "a");
      Term b = solver.mkConst(intSort, "b");
      //! [docs-java-quickstart-4 end]

      // Our constraints regarding x and y will be:
      //
      //   (1)  0 < x
      //   (2)  0 < y
      //   (3)  x + y < 1
      //   (4)  x <= y
      //

      //! [docs-java-quickstart-5 start]
      // Formally, constraints are also terms. Their sort is Boolean.
      // We will construct these constraints gradually,
      // by defining each of their components.
      // We start with the constant numerals 0 and 1:
      Term zero = solver.mkReal(0);
      Term one = solver.mkReal(1);

      // Next, we construct the term x + y
      Term xPlusY = solver.mkTerm(Kind.ADD, x, y);

      // Now we can define the constraints.
      // They use the operators +, <=, and <.
      // In the API, these are denoted by ADD, LEQ, and LT.
      // A list of available operators is available in:
      // src/api/cpp/cvc5_kind.h
      Term constraint1 = solver.mkTerm(Kind.LT, zero, x);
      Term constraint2 = solver.mkTerm(Kind.LT, zero, y);
      Term constraint3 = solver.mkTerm(Kind.LT, xPlusY, one);
      Term constraint4 = solver.mkTerm(Kind.LEQ, x, y);

      // Now we assert the constraints to the solver.
      solver.assertFormula(constraint1);
      solver.assertFormula(constraint2);
      solver.assertFormula(constraint3);
      solver.assertFormula(constraint4);
      //! [docs-java-quickstart-5 end]

      // Check if the formula is satisfiable, that is,
      // are there real values for x and y that satisfy all the constraints?
      //! [docs-java-quickstart-6 start]
      Result r1 = solver.checkSat();
      //! [docs-java-quickstart-6 end]

      // The result is either SAT, UNSAT, or UNKNOWN.
      // In this case, it is SAT.
      //! [docs-java-quickstart-7 start]
      System.out.println("expected: sat");
      System.out.println("result: " + r1);
      //! [docs-java-quickstart-7 end]

      // We can get the values for x and y that satisfy the constraints.
      //! [docs-java-quickstart-8 start]
      Term xVal = solver.getValue(x);
      Term yVal = solver.getValue(y);
      //! [docs-java-quickstart-8 end]

      // It is also possible to get values for compound terms,
      // even if those did not appear in the original formula.
      //! [docs-java-quickstart-9 start]
      Term xMinusY = solver.mkTerm(Kind.SUB, x, y);
      Term xMinusYVal = solver.getValue(xMinusY);
      //! [docs-java-quickstart-9 end]

      // Further, we can convert the values to java types
      //! [docs-java-quickstart-10 start]
      Pair<BigInteger, BigInteger> xPair = xVal.getRealValue();
      Pair<BigInteger, BigInteger> yPair = yVal.getRealValue();
      Pair<BigInteger, BigInteger> xMinusYPair = xMinusYVal.getRealValue();

      System.out.println("value for x: " + xPair.first + "/" + xPair.second);
      System.out.println("value for y: " + yPair.first + "/" + yPair.second);
      System.out.println("value for x - y: " + xMinusYPair.first + "/" + xMinusYPair.second);
      //! [docs-java-quickstart-10 end]

      // Another way to independently compute the value of x - y would be
      // to perform the (rational) arithmetic manually.
      // However, for more complex terms,
      // it is easier to let the solver do the evaluation.
      //! [docs-java-quickstart-11 start]
      Pair<BigInteger, BigInteger> xMinusYComputed =
          new Pair(xPair.first.multiply(yPair.second).subtract(xPair.second.multiply(yPair.first)),
              xPair.second.multiply(yPair.second));
      BigInteger g = xMinusYComputed.first.gcd(xMinusYComputed.second);
      xMinusYComputed = new Pair(xMinusYComputed.first.divide(g), xMinusYComputed.second.divide(g));
      if (xMinusYComputed.equals(xMinusYPair))
      {
        System.out.println("computed correctly");
      }
      else
      {
        System.out.println("computed incorrectly");
      }
      //! [docs-java-quickstart-11 end]

      // Next, we will check satisfiability of the same formula,
      // only this time over integer variables a and b.

      // We start by resetting assertions added to the solver.
      //! [docs-java-quickstart-12 start]
      solver.resetAssertions();
      //! [docs-java-quickstart-12 end]

      // Next, we assert the same assertions above with integers.
      // This time, we inline the construction of terms
      // to the assertion command.
      //! [docs-java-quickstart-13 start]
      solver.assertFormula(solver.mkTerm(Kind.LT, solver.mkInteger(0), a));
      solver.assertFormula(solver.mkTerm(Kind.LT, solver.mkInteger(0), b));
      solver.assertFormula(
          solver.mkTerm(Kind.LT, solver.mkTerm(Kind.ADD, a, b), solver.mkInteger(1)));
      solver.assertFormula(solver.mkTerm(Kind.LEQ, a, b));
      //! [docs-java-quickstart-13 end]

      // We check whether the revised assertion is satisfiable.
      //! [docs-java-quickstart-14 start]
      Result r2 = solver.checkSat();

      // This time the formula is unsatisfiable
      System.out.println("expected: unsat");
      System.out.println("result: " + r2);
      //! [docs-java-quickstart-14 end]

      // We can query the solver for an unsatisfiable core, i.e., a subset
      // of the assertions that is already unsatisfiable.
      //! [docs-java-quickstart-15 start]
      List<Term> unsatCore = Arrays.asList(solver.getUnsatCore());
      System.out.println("unsat core size: " + unsatCore.size());
      System.out.println("unsat core: ");
      for (Term t : unsatCore)
      {
        System.out.println(t);
      }
      //! [docs-java-quickstart-15 end]
    }
  }
}
