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
 * Catching cvc5 exceptions via the Java API.
 *
 * A simple demonstration of catching cvc5 execptions via the Java API.
 */

import io.github.cvc5.*;

public class Exceptions
{
  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    {
      solver.setOption("produce-models", "true");

      // Setting an invalid option
      try
      {
        solver.setOption("non-existing", "true");
        System.exit(1);
      }
      catch (Exception e)
      {
        System.out.println(e.toString());
      }

      // Creating a term with an invalid type
      try
      {
        Sort integer = tm.getIntegerSort();
        Term x = tm.mkVar(integer, "x");
        Term invalidTerm = tm.mkTerm(Kind.AND, x, x);
        solver.checkSatAssuming(invalidTerm);
        System.exit(1);
      }
      catch (Exception e)
      {
        System.out.println(e.toString());
      }

      // Asking for a model after unsat result
      try
      {
        solver.checkSatAssuming(tm.mkBoolean(false));
        solver.getModel(new Sort[] {}, new Term[] {});
        System.exit(1);
      }
      catch (Exception e)
      {
        System.out.println(e.toString());
      }
    }
    Context.deletePointers();
  }
}
