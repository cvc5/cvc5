/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Daniel Larraz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of solving finite field problems with cvc5's Java API
 *
 */

import io.github.cvc5.*;
import java.util.*;

public class FiniteField
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setLogic("QF_FF"); // Set the logic

      Sort f5 = tm.mkFiniteFieldSort("5", 10);
      Term a = tm.mkConst(f5, "a");
      Term b = tm.mkConst(f5, "b");
      Term z = tm.mkFiniteFieldElem("0", f5, 10);

      System.out.println("is ff: " + f5.isFiniteField());
      System.out.println("ff size: " + f5.getFiniteFieldSize());
      System.out.println("is ff value: " + z.isFiniteFieldValue());
      System.out.println("ff value: " + z.getFiniteFieldValue());

      Term inv = tm.mkTerm(Kind.EQUAL,
          tm.mkTerm(Kind.FINITE_FIELD_ADD,
              tm.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
              tm.mkFiniteFieldElem("-1", f5, 10)),
          z);

      Term aIsTwo = tm.mkTerm(
          Kind.EQUAL, tm.mkTerm(Kind.FINITE_FIELD_ADD, a, tm.mkFiniteFieldElem("-2", f5, 10)), z);

      slv.assertFormula(inv);
      slv.assertFormula(aIsTwo);

      Result r = slv.checkSat();
      System.out.println("is sat: " + r.isSat());

      Term bIsTwo = tm.mkTerm(
          Kind.EQUAL, tm.mkTerm(Kind.FINITE_FIELD_ADD, b, tm.mkFiniteFieldElem("-2", f5, 10)), z);

      slv.assertFormula(bIsTwo);
      r = slv.checkSat();
      System.out.println("is sat: " + r.isSat());
    }
    Context.deletePointers();
  }
}
