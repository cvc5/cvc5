/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Daniel Larraz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the transcendental extension.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class Transcendentals
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setLogic("QF_NRAT");

      Sort real = tm.getRealSort();

      // Variables
      Term x = tm.mkConst(real, "x");
      Term y = tm.mkConst(real, "y");

      // Helper terms
      Term two = tm.mkReal(2);
      Term pi = tm.mkPi();
      Term twopi = tm.mkTerm(MULT, two, pi);
      Term ysq = tm.mkTerm(MULT, y, y);
      Term sinx = tm.mkTerm(SINE, x);

      // Formulas
      Term x_gt_pi = tm.mkTerm(GT, x, pi);
      Term x_lt_tpi = tm.mkTerm(LT, x, twopi);
      Term ysq_lt_sinx = tm.mkTerm(LT, ysq, sinx);

      slv.assertFormula(x_gt_pi);
      slv.assertFormula(x_lt_tpi);
      slv.assertFormula(ysq_lt_sinx);

      System.out.println("cvc5 should report UNSAT.");
      System.out.println("Result from cvc5 is: " + slv.checkSat());
    }
    Context.deletePointers();
  }
}
