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
 * A simple demonstration of the capabilities of cvc5
 *
 * A simple demonstration of how to use uninterpreted functions, combining this
 * with arithmetic, and extracting a model at the end of a satisfiable query.
 * The model is displayed using getValue().
 */

import io.github.cvc5.*;
import java.util.Iterator;

public class Combination
{
  private static void prefixPrintGetValue(Solver slv, Term t)
  {
    prefixPrintGetValue(slv, t, 0);
  }

  private static void prefixPrintGetValue(Solver slv, Term t, int level)
  {
    System.out.println("slv.getValue(" + t + "): " + slv.getValue(t));

    for (Term c : t)
    {
      prefixPrintGetValue(slv, c, level + 1);
    }
  }

  public static void main(String[] args) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setOption("produce-models", "true"); // Produce Models
      slv.setOption("dag-thresh", "0"); // Disable dagifying the output
      slv.setOption("output-language", "smt2"); // use smt-lib v2 as output language
      slv.setLogic("QF_UFLIRA");

      // Sorts
      Sort u = tm.mkUninterpretedSort("u");
      Sort integer = tm.getIntegerSort();
      Sort bool = tm.getBooleanSort();
      Sort uToInt = tm.mkFunctionSort(u, integer);
      Sort intPred = tm.mkFunctionSort(integer, bool);

      // Variables
      Term x = tm.mkConst(u, "x");
      Term y = tm.mkConst(u, "y");

      // Functions
      Term f = tm.mkConst(uToInt, "f");
      Term p = tm.mkConst(intPred, "p");

      // Constants
      Term zero = tm.mkInteger(0);
      Term one = tm.mkInteger(1);

      // Terms
      Term f_x = tm.mkTerm(Kind.APPLY_UF, f, x);
      Term f_y = tm.mkTerm(Kind.APPLY_UF, f, y);
      Term sum = tm.mkTerm(Kind.ADD, f_x, f_y);
      Term p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero);
      Term p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y);

      // Construct the assertions
      Term assertions = tm.mkTerm(Kind.AND,
          new Term[] {
              tm.mkTerm(Kind.LEQ, zero, f_x), // 0 <= f(x)
              tm.mkTerm(Kind.LEQ, zero, f_y), // 0 <= f(y)
              tm.mkTerm(Kind.LEQ, sum, one), // f(x) + f(y) <= 1
              p_0.notTerm(), // not p(0)
              p_f_y // p(f(y))
          });
      slv.assertFormula(assertions);

      System.out.println("Given the following assertions:\n" + assertions + "\n");

      System.out.println("Prove x /= y is entailed. \n"
          + "cvc5: " + slv.checkSatAssuming(tm.mkTerm(Kind.EQUAL, x, y)) + ".\n");

      System.out.println("Call checkSat to show that the assertions are satisfiable. \n"
          + "cvc5: " + slv.checkSat() + ".\n");

      System.out.println("Call slv.getValue(...) on terms of interest.");
      System.out.println("slv.getValue(" + f_x + "): " + slv.getValue(f_x));
      System.out.println("slv.getValue(" + f_y + "): " + slv.getValue(f_y));
      System.out.println("slv.getValue(" + sum + "): " + slv.getValue(sum));
      System.out.println("slv.getValue(" + p_0 + "): " + slv.getValue(p_0));
      System.out.println("slv.getValue(" + p_f_y + "): " + slv.getValue(p_f_y) + "\n");

      System.out.println("Alternatively, iterate over assertions and call slv.getValue(...) "
          + "on all terms.");
      prefixPrintGetValue(slv, assertions);

      System.out.println();
      System.out.println("You can also use nested loops to iterate over terms.");
      Iterator<Term> it1 = assertions.iterator();
      while (it1.hasNext())
      {
        Term t = it1.next();
        System.out.println("term: " + t);
        Iterator<Term> it2 = t.iterator();
        while (it2.hasNext())
        {
          System.out.println(" + child: " + it2.next());
        }
      }
      System.out.println();
      System.out.println("Alternatively, you can also use for-each loops.");
      for (Term t : assertions)
      {
        System.out.println("term: " + t);
        for (Term c : t)
        {
          System.out.println(" + child: " + c);
        }
      }
    }
    Context.deletePointers();
  }
}
