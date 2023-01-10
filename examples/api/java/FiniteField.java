/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Mudathir Mohamed, Liana Hadarean, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
    Solver slv = new Solver();
    {
      slv.setLogic("QF_FF"); // Set the logic

      Sort f5 = slv.mkFiniteFieldSort("5");
      Term a = slv.mkConst(f5, "a");
      Term b = slv.mkConst(f5, "b");
      Term z = slv.mkFiniteFieldElem("0", f5);

      System.out.println("is ff: " + f5.isFiniteField());
      System.out.println("ff size: " + f5.getFiniteFieldSize());
      System.out.println("is ff value: " + z.isFiniteFieldValue());
      System.out.println("ff value: " + z.getFiniteFieldValue());

      Term inv =
        slv.mkTerm(Kind.EQUAL,
            slv.mkTerm(Kind.FINITE_FIELD_ADD,
              slv.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
              slv.mkFiniteFieldElem("-1", f5)),
            z);

      Term aIsTwo =
        slv.mkTerm(Kind.EQUAL,
            slv.mkTerm(Kind.FINITE_FIELD_ADD,
              a,
              slv.mkFiniteFieldElem("-2", f5)),
            z);

      slv.assertFormula(inv);
      slv.assertFormula(aIsTwo);

      Result r = slv.checkSat();
      System.out.println("is sat: " + r.isSat());

      Term bIsTwo =
        slv.mkTerm(Kind.EQUAL,
            slv.mkTerm(Kind.FINITE_FIELD_ADD,
              b,
              slv.mkFiniteFieldElem("-2", f5)),
            z);

      slv.assertFormula(bIsTwo);
      r = slv.checkSat();
      System.out.println("is sat: " + r.isSat());
    }
  }
}
