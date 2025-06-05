/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Daniel Larraz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the linear arithmetic solving capabilities and
 * the push pop of cvc5. This also gives an example option.
 */

import io.github.cvc5.*;
public class LinearArith
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setLogic("QF_LIRA"); // Set the logic

      // Prove that if given x (Integer) and y (Real) then
      // the maximum value of y - x is 2/3

      // Sorts
      Sort real = tm.getRealSort();
      Sort integer = tm.getIntegerSort();

      // Variables
      Term x = tm.mkConst(integer, "x");
      Term y = tm.mkConst(real, "y");

      // Constants
      Term three = tm.mkInteger(3);
      Term neg2 = tm.mkInteger(-2);
      Term two_thirds = tm.mkReal(2, 3);

      // Terms
      Term three_y = tm.mkTerm(Kind.MULT, three, y);
      Term diff = tm.mkTerm(Kind.SUB, y, x);

      // Formulas
      Term x_geq_3y = tm.mkTerm(Kind.GEQ, x, three_y);
      Term x_leq_y = tm.mkTerm(Kind.LEQ, x, y);
      Term neg2_lt_x = tm.mkTerm(Kind.LT, neg2, x);

      Term assertions = tm.mkTerm(Kind.AND, x_geq_3y, x_leq_y, neg2_lt_x);

      System.out.println("Given the assertions " + assertions);
      slv.assertFormula(assertions);

      slv.push();
      Term diff_leq_two_thirds = tm.mkTerm(Kind.LEQ, diff, two_thirds);
      System.out.println("Prove that " + diff_leq_two_thirds + " with cvc5.");
      System.out.println("cvc5 should report UNSAT.");
      System.out.println(
          "Result from cvc5 is: " + slv.checkSatAssuming(diff_leq_two_thirds.notTerm()));
      slv.pop();

      System.out.println();

      slv.push();
      Term diff_is_two_thirds = tm.mkTerm(Kind.EQUAL, diff, two_thirds);
      slv.assertFormula(diff_is_two_thirds);
      System.out.println("Show that the assertions are consistent with ");
      System.out.println(diff_is_two_thirds + " with cvc5.");
      System.out.println("cvc5 should report SAT.");
      System.out.println("Result from cvc5 is: " + slv.checkSat());
      slv.pop();

      System.out.println("Thus the maximum value of (y - x) is 2/3.");
    }
    Context.deletePointers();
  }
}
