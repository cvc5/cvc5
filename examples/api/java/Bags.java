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
 * A simple demonstration of reasoning about bags with cvc5.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class Bags
{
  public static void main(String args[]) throws CVC5ApiException

  {
    Solver slv = new Solver();
    {
      slv.setLogic("ALL");

      // Produce models
      slv.setOption("produce-models", "true");
      slv.setOption("incremental", "true");

      Sort bag = slv.mkBagSort(slv.getStringSort());
      Term A = slv.mkConst(bag, "A");
      Term B = slv.mkConst(bag, "B");
      Term C = slv.mkConst(bag, "C");
      Term x = slv.mkConst(slv.getStringSort(), "x");

      Term intersectionAC = slv.mkTerm(BAG_INTER_MIN, new Term[] {A, C});
      Term intersectionBC = slv.mkTerm(BAG_INTER_MIN, new Term[] {B, C});

      // union disjoint does not distribute over intersection
      {
        Term unionDisjointAB = slv.mkTerm(BAG_UNION_DISJOINT, new Term[] {A, B});
        Term lhs = slv.mkTerm(BAG_INTER_MIN, new Term[] {unionDisjointAB, C});
        Term rhs = slv.mkTerm(BAG_UNION_DISJOINT, new Term[] {intersectionAC, intersectionBC});
        Term guess = slv.mkTerm(EQUAL, new Term[] {lhs, rhs});

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
        Term unionMaxAB = slv.mkTerm(BAG_UNION_MAX, new Term[] {A, B});
        Term lhs = slv.mkTerm(BAG_INTER_MIN, new Term[] {unionMaxAB, C});
        Term rhs = slv.mkTerm(BAG_UNION_MAX, new Term[] {intersectionAC, intersectionBC});
        Term theorem = slv.mkTerm(EQUAL, new Term[] {lhs, rhs});
        System.out.println("cvc5 reports: " + theorem.notTerm() + " is "
            + slv.checkSatAssuming(theorem.notTerm()) + ".");
      }

      // Verify emptbag is a subbag of any bag
      {
        Term emptybag = slv.mkEmptyBag(bag);
        Term theorem = slv.mkTerm(BAG_SUBBAG, new Term[] {emptybag, A});

        System.out.println("cvc5 reports: " + theorem.notTerm() + " is "
            + slv.checkSatAssuming(theorem.notTerm()) + ".");
      }

      // find an element with multiplicity 4 in the disjoint union of
      // ; {|"a", "a", "b", "b", "b"|} and {|"b", "c", "c"|}
      {
        Term one = slv.mkInteger(1);
        Term two = slv.mkInteger(2);
        Term three = slv.mkInteger(3);
        Term four = slv.mkInteger(4);
        Term a = slv.mkString("a");
        Term b = slv.mkString("b");
        Term c = slv.mkString("c");

        Term bag_a_2 = slv.mkTerm(BAG_MAKE, new Term[] {a, two});
        Term bag_b_3 = slv.mkTerm(BAG_MAKE, new Term[] {b, three});
        Term bag_b_1 = slv.mkTerm(BAG_MAKE, new Term[] {b, one});
        Term bag_c_2 = slv.mkTerm(BAG_MAKE, new Term[] {c, two});

        Term bag_a_2_b_3 = slv.mkTerm(BAG_UNION_DISJOINT, new Term[] {bag_a_2, bag_b_3});

        Term bag_b_1_c_2 = slv.mkTerm(BAG_UNION_DISJOINT, new Term[] {bag_b_1, bag_c_2});

        Term union_disjoint = slv.mkTerm(BAG_UNION_DISJOINT, new Term[] {bag_a_2_b_3, bag_b_1_c_2});

        Term count_x = slv.mkTerm(BAG_COUNT, new Term[] {x, union_disjoint});
        Term e = slv.mkTerm(EQUAL, new Term[] {four, count_x});
        Result result = slv.checkSatAssuming(e);

        System.out.println("cvc5 reports: " + e + " is " + result + ".");
        if (result.isSat())
        {
          System.out.println(x + ": " + slv.getValue(x));
        }
      }
    }
  }
}