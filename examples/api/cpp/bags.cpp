/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about bags.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  Solver slv;
  slv.setLogic("ALL");
  // Produce models
  slv.setOption("produce-models", "true");
  slv.setOption("incremental", "true");

  Sort bag = slv.mkBagSort(slv.getStringSort());
  Term A = slv.mkConst(bag, "A");
  Term B = slv.mkConst(bag, "B");
  Term C = slv.mkConst(bag, "C");
  Term x = slv.mkConst(slv.getStringSort(), "x");

  Term intersectionAC = slv.mkTerm(BAG_INTER_MIN, {A, C});
  Term intersectionBC = slv.mkTerm(BAG_INTER_MIN, {B, C});

  // union disjoint does not distribute over intersection
  {
    Term unionDisjointAB = slv.mkTerm(BAG_UNION_DISJOINT, {A, B});
    Term lhs = slv.mkTerm(BAG_INTER_MIN, {unionDisjointAB, C});
    Term rhs = slv.mkTerm(BAG_UNION_DISJOINT, {intersectionAC, intersectionBC});
    Term guess = slv.mkTerm(EQUAL, {lhs, rhs});
    cout << "cvc5 reports: " << guess.notTerm() << " is "
         << slv.checkSatAssuming(guess.notTerm()) << "." << endl;

    cout << A << ": " << slv.getValue(A) << endl;
    cout << B << ": " << slv.getValue(B) << endl;
    cout << C << ": " << slv.getValue(C) << endl;
    cout << lhs << ": " << slv.getValue(lhs) << endl;
    cout << rhs << ": " << slv.getValue(rhs) << endl;
  }

  // union max distributes over intersection
  {
    Term unionMaxAB = slv.mkTerm(BAG_UNION_MAX, {A, B});
    Term lhs = slv.mkTerm(BAG_INTER_MIN, {unionMaxAB, C});
    Term rhs = slv.mkTerm(BAG_UNION_MAX, {intersectionAC, intersectionBC});
    Term theorem = slv.mkTerm(EQUAL, {lhs, rhs});
    cout << "cvc5 reports: " << theorem.notTerm() << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
  }

  // Verify emptbag is a subbag of any bag
  {
    Term emptybag = slv.mkEmptyBag(bag);
    Term theorem = slv.mkTerm(BAG_SUBBAG, {emptybag, A});

    cout << "cvc5 reports: " << theorem.notTerm() << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
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

    Term bag_a_2 = slv.mkTerm(BAG_MAKE, {a, two});
    Term bag_b_3 = slv.mkTerm(BAG_MAKE, {b, three});
    Term bag_b_1 = slv.mkTerm(BAG_MAKE, {b, one});
    Term bag_c_2 = slv.mkTerm(BAG_MAKE, {c, two});
    Term bag_a_2_b_3 = slv.mkTerm(BAG_UNION_DISJOINT, {bag_a_2, bag_b_3});
    Term bag_b_1_c_2 = slv.mkTerm(BAG_UNION_DISJOINT, {bag_b_1, bag_c_2});
    Term union_disjoint =
        slv.mkTerm(BAG_UNION_DISJOINT, {bag_a_2_b_3, bag_b_1_c_2});

    Term count_x = slv.mkTerm(BAG_COUNT, {x, union_disjoint});
    Term e = slv.mkTerm(EQUAL, {four, count_x});
    Result result = slv.checkSatAssuming(e);

    cout << "cvc5 reports: " << e << " is " << result << "." << endl;
    if (result.isSat())
    {
      cout << x << ": " << slv.getValue(x) << endl;
    }
  }
}
