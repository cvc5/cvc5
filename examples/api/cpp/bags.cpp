/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("ALL");
  // Produce models
  slv.setOption("produce-models", "true");
  slv.setOption("incremental", "true");

  Sort bag = tm.mkBagSort(tm.getStringSort());
  Term A = tm.mkConst(bag, "A");
  Term B = tm.mkConst(bag, "B");
  Term C = tm.mkConst(bag, "C");
  Term x = tm.mkConst(tm.getStringSort(), "x");

  Term intersectionAC = tm.mkTerm(Kind::BAG_INTER_MIN, {A, C});
  Term intersectionBC = tm.mkTerm(Kind::BAG_INTER_MIN, {B, C});

  // union disjoint does not distribute over intersection
  {
    Term unionDisjointAB = tm.mkTerm(Kind::BAG_UNION_DISJOINT, {A, B});
    Term lhs = tm.mkTerm(Kind::BAG_INTER_MIN, {unionDisjointAB, C});
    Term rhs =
        tm.mkTerm(Kind::BAG_UNION_DISJOINT, {intersectionAC, intersectionBC});
    Term guess = tm.mkTerm(Kind::EQUAL, {lhs, rhs});
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
    Term unionMaxAB = tm.mkTerm(Kind::BAG_UNION_MAX, {A, B});
    Term lhs = tm.mkTerm(Kind::BAG_INTER_MIN, {unionMaxAB, C});
    Term rhs = tm.mkTerm(Kind::BAG_UNION_MAX, {intersectionAC, intersectionBC});
    Term theorem = tm.mkTerm(Kind::EQUAL, {lhs, rhs});
    cout << "cvc5 reports: " << theorem.notTerm() << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
  }

  // Verify emptbag is a subbag of any bag
  {
    Term emptybag = tm.mkEmptyBag(bag);
    Term theorem = tm.mkTerm(Kind::BAG_SUBBAG, {emptybag, A});

    cout << "cvc5 reports: " << theorem.notTerm() << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
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

    Term bag_a_2 = tm.mkTerm(Kind::BAG_MAKE, {a, two});
    Term bag_b_3 = tm.mkTerm(Kind::BAG_MAKE, {b, three});
    Term bag_b_1 = tm.mkTerm(Kind::BAG_MAKE, {b, one});
    Term bag_c_2 = tm.mkTerm(Kind::BAG_MAKE, {c, two});
    Term bag_a_2_b_3 = tm.mkTerm(Kind::BAG_UNION_DISJOINT, {bag_a_2, bag_b_3});
    Term bag_b_1_c_2 = tm.mkTerm(Kind::BAG_UNION_DISJOINT, {bag_b_1, bag_c_2});
    Term union_disjoint =
        tm.mkTerm(Kind::BAG_UNION_DISJOINT, {bag_a_2_b_3, bag_b_1_c_2});

    Term count_x = tm.mkTerm(Kind::BAG_COUNT, {x, union_disjoint});
    Term e = tm.mkTerm(Kind::EQUAL, {four, count_x});
    Result result = slv.checkSatAssuming(e);

    cout << "cvc5 reports: " << e << " is " << result << "." << endl;
    if (result.isSat())
    {
      cout << x << ": " << slv.getValue(x) << endl;
    }
  }
}
