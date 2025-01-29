/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of interacting with unsat cores using cvc5's Java API.
 */

import io.github.cvc5.*;
import java.util.Arrays;

public class UnsatCores
{
  public static void main(String[] args) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    {
      // Enable the production of unsat cores
      solver.setOption("produce-unsat-cores", "true");

      Sort boolSort = tm.getBooleanSort();
      Term a = tm.mkConst(boolSort, "A");
      Term b = tm.mkConst(boolSort, "B");

      // A ^ B
      solver.assertFormula(tm.mkTerm(Kind.AND, a, b));
      // ~(A v B)
      solver.assertFormula(tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.OR, a, b)));

      Result res = solver.checkSat(); // result is unsat

      // Retrieve the unsat core
      Term[] unsatCore = solver.getUnsatCore();

      // Print the unsat core
      System.out.println("Unsat Core: " + Arrays.asList(unsatCore));

      // Iterate over expressions in the unsat core.
      System.out.println("--- Unsat Core ---");
      for (Term e : unsatCore)
      {
        System.out.println(e);
      }
    }
    Context.deletePointers();
  }
}
