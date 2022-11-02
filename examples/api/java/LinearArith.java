/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
    Solver slv = new Solver();
    {
      slv.setLogic("QF_LIRA"); // Set the logic

      // Prove that if given x (Integer) and y (Real) then
      // the maximum value of y - x is 2/3

      // Sorts
      Sort real = slv.getRealSort();
      Sort integer = slv.getIntegerSort();

      // Variables
      Term x = slv.mkConst(integer, "x");
      Term y = slv.mkConst(real, "y");

      // Constants
      Term three = slv.mkInteger(3);
      Term neg2 = slv.mkInteger(-2);
      Term two_thirds = slv.mkReal(2, 3);

      // Terms
      Term three_y = slv.mkTerm(Kind.MULT, three, y);
      Term diff = slv.mkTerm(Kind.SUB, y, x);

      // Formulas
      Term x_geq_3y = slv.mkTerm(Kind.GEQ, x, three_y);
      Term x_leq_y = slv.mkTerm(Kind.LEQ, x, y);
      Term neg2_lt_x = slv.mkTerm(Kind.LT, neg2, x);

      Term assertions = slv.mkTerm(Kind.AND, x_geq_3y, x_leq_y, neg2_lt_x);

      System.out.println("Given the assertions " + assertions);
      slv.assertFormula(assertions);

      slv.push();
      Term diff_leq_two_thirds = slv.mkTerm(Kind.LEQ, diff, two_thirds);
      System.out.println("Prove that " + diff_leq_two_thirds + " with cvc5.");
      System.out.println("cvc5 should report UNSAT.");
      System.out.println(
          "Result from cvc5 is: " + slv.checkSatAssuming(diff_leq_two_thirds.notTerm()));
      slv.pop();

      System.out.println();

      slv.push();
      Term diff_is_two_thirds = slv.mkTerm(Kind.EQUAL, diff, two_thirds);
      slv.assertFormula(diff_is_two_thirds);
      System.out.println("Show that the assertions are consistent with ");
      System.out.println(diff_is_two_thirds + " with cvc5.");
      System.out.println("cvc5 should report SAT.");
      System.out.println("Result from cvc5 is: " + slv.checkSat());
      slv.pop();

      System.out.println("Thus the maximum value of (y - x) is 2/3.");
    }
  }
}
