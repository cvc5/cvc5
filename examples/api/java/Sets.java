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
 * A simple demonstration of reasoning about sets with cvc5.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class Sets
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      // Optionally, set the logic. We need at least UF for equality predicate,
      // integers (LIA) and sets (FS).
      slv.setLogic("QF_UFLIAFS");

      // Produce models
      slv.setOption("produce-models", "true");
      slv.setOption("output-language", "smt2");

      Sort integer = tm.getIntegerSort();
      Sort set = tm.mkSetSort(integer);

      // Verify union distributions over intersection
      // (A union B) intersection C = (A intersection C) union (B intersection C)
      {
        Term A = tm.mkConst(set, "A");
        Term B = tm.mkConst(set, "B");
        Term C = tm.mkConst(set, "C");

        Term unionAB = tm.mkTerm(SET_UNION, A, B);
        Term lhs = tm.mkTerm(SET_INTER, unionAB, C);

        Term intersectionAC = tm.mkTerm(SET_INTER, A, C);
        Term intersectionBC = tm.mkTerm(SET_INTER, B, C);
        Term rhs = tm.mkTerm(SET_UNION, intersectionAC, intersectionBC);

        Term theorem = tm.mkTerm(EQUAL, lhs, rhs);

        System.out.println(
            "cvc5 reports: " + theorem + " is " + slv.checkSatAssuming(theorem.notTerm()) + ".");
      }

      // Verify set.empty is a subset of any set
      {
        Term A = tm.mkConst(set, "A");
        Term emptyset = tm.mkEmptySet(set);

        Term theorem = tm.mkTerm(SET_SUBSET, emptyset, A);

        System.out.println(
            "cvc5 reports: " + theorem + " is " + slv.checkSatAssuming(theorem.notTerm()) + ".");
      }

      // Find me an element in {1, 2} intersection {2, 3}, if there is one.
      {
        Term one = tm.mkInteger(1);
        Term two = tm.mkInteger(2);
        Term three = tm.mkInteger(3);

        Term singleton_one = tm.mkTerm(SET_SINGLETON, one);
        Term singleton_two = tm.mkTerm(SET_SINGLETON, two);
        Term singleton_three = tm.mkTerm(SET_SINGLETON, three);
        Term one_two = tm.mkTerm(SET_UNION, singleton_one, singleton_two);
        Term two_three = tm.mkTerm(SET_UNION, singleton_two, singleton_three);
        Term intersection = tm.mkTerm(SET_INTER, one_two, two_three);

        Term x = tm.mkConst(integer, "x");

        Term e = tm.mkTerm(SET_MEMBER, x, intersection);

        Result result = slv.checkSatAssuming(e);
        System.out.println("cvc5 reports: " + e + " is " + result + ".");

        if (result.isSat())
        {
          System.out.println("For instance, " + slv.getValue(x) + " is a member.");
        }
      }
    }
    Context.deletePointers();
  }
}
