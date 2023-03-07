/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
    Solver solver = new Solver();
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
        Sort integer = solver.getIntegerSort();
        Term x = solver.mkVar(integer, "x");
        Term invalidTerm = solver.mkTerm(Kind.AND, x, x);
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
        solver.checkSatAssuming(solver.mkBoolean(false));
        solver.getModel(new Sort[] {}, new Term[] {});
        System.exit(1);
      }
      catch (Exception e)
      {
        System.out.println(e.toString());
      }
    }
  }
}
