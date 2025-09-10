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
 * A simple demonstration of reasoning about bags with cvc5.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class Bags
{
  public static void main(String args[]) throws CVC5ApiException

  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setLogic("ALL");

      // Produce models
      slv.setOption("produce-models", "true");
      slv.setOption("incremental", "true");

      Sort bag = tm.mkBagSort(tm.getStringSort());
      Term A = tm.mkConst(bag, "A");
      Term B = tm.mkConst(bag, "B");
      Term C = tm.mkConst(bag, "C");
      Term x = tm.mkConst(tm.getStringSort(), "x");

      Term intersectionAC = tm.mkTerm(BAG_INTER_MIN, new Term[] {A, C});
      Term intersectionBC = tm.mkTerm(BAG_INTER_MIN, new Term[] {B, C});

      // union disjoint does not distribute over intersection
      {
        Term unionDisjointAB = tm.mkTerm(BAG_UNION_DISJOINT, new Term[] {A, B});
        Term lhs = tm.mkTerm(BAG_INTER_MIN, new Term[] {unionDisjointAB, C});
        Term rhs = tm.mkTerm(BAG_UNION_DISJOINT, new Term[] {intersectionAC, intersectionBC});
        Term guess = tm.mkTerm(EQUAL, new Term[] {lhs, rhs});

        System.out.println("cvc5 reports: " + guess.notTerm() + " is "
            + slv.checkSatAssuming(guess.notTerm()) + ".");

        System.out.println(A + ": " + slv.getValue(A));
        System.out.println(B + ": " + slv.getValue(B));
        System.out.println(C + ": " + slv.getValue(C));
        System.out.println(lhs + ": " + slv.getValue(lhs));
        System.out.println(rhs + ": " + slv.getValue(rhs));
      }

      // union max distributes over intersection
      {
        Term unionMaxAB = tm.mkTerm(BAG_UNION_MAX, new Term[] {A, B});
        Term lhs = tm.mkTerm(BAG_INTER_MIN, new Term[] {unionMaxAB, C});
        Term rhs = tm.mkTerm(BAG_UNION_MAX, new Term[] {intersectionAC, intersectionBC});
        Term theorem = tm.mkTerm(EQUAL, new Term[] {lhs, rhs});
        System.out.println("cvc5 reports: " + theorem.notTerm() + " is "
            + slv.checkSatAssuming(theorem.notTerm()) + ".");
      }

      // Verify emptbag is a subbag of any bag
      {
        Term emptybag = tm.mkEmptyBag(bag);
        Term theorem = tm.mkTerm(BAG_SUBBAG, new Term[] {emptybag, A});

        System.out.println("cvc5 reports: " + theorem.notTerm() + " is "
            + slv.checkSatAssuming(theorem.notTerm()) + ".");
      }

      // find an element with multiplicity 4 in the disjoint union of
      // ; {|"a", "a", "b", "b", "b"|} and {|"b", "c", "c"|}
      {
        Term one = tm.mkInteger(1);
        Term two = tm.mkInteger(2);
        Term three = tm.mkInteger(3);
        Term four = tm.mkInteger(4);
        Term a = tm.mkString("a");
        Term b = tm.mkString("b");
        Term c = tm.mkString("c");

        Term bag_a_2 = tm.mkTerm(BAG_MAKE, new Term[] {a, two});
        Term bag_b_3 = tm.mkTerm(BAG_MAKE, new Term[] {b, three});
        Term bag_b_1 = tm.mkTerm(BAG_MAKE, new Term[] {b, one});
        Term bag_c_2 = tm.mkTerm(BAG_MAKE, new Term[] {c, two});

        Term bag_a_2_b_3 = tm.mkTerm(BAG_UNION_DISJOINT, new Term[] {bag_a_2, bag_b_3});

        Term bag_b_1_c_2 = tm.mkTerm(BAG_UNION_DISJOINT, new Term[] {bag_b_1, bag_c_2});

        Term union_disjoint = tm.mkTerm(BAG_UNION_DISJOINT, new Term[] {bag_a_2_b_3, bag_b_1_c_2});

        Term count_x = tm.mkTerm(BAG_COUNT, new Term[] {x, union_disjoint});
        Term e = tm.mkTerm(EQUAL, new Term[] {four, count_x});
        Result result = slv.checkSatAssuming(e);

        System.out.println("cvc5 reports: " + e + " is " + result + ".");
        if (result.isSat())
        {
          System.out.println(x + ": " + slv.getValue(x));
        }
      }
    }
    Context.deletePointers();
  }
}