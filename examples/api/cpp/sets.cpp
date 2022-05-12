/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Kshitij Bansal, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about sets with cvc5.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  Solver slv;

  // Optionally, set the logic. We need at least UF for equality predicate,
  // integers (LIA) and sets (FS).
  slv.setLogic("QF_UFLIAFS");

  // Produce models
  slv.setOption("produce-models", "true");
  slv.setOption("output-language", "smt2");

  Sort integer = slv.getIntegerSort();
  Sort set = slv.mkSetSort(integer);

  // Verify union distributions over intersection
  // (A union B) intersection C = (A intersection C) union (B intersection C)
  {
    Term A = slv.mkConst(set, "A");
    Term B = slv.mkConst(set, "B");
    Term C = slv.mkConst(set, "C");

    Term unionAB = slv.mkTerm(SET_UNION, {A, B});
    Term lhs = slv.mkTerm(SET_INTER, {unionAB, C});

    Term intersectionAC = slv.mkTerm(SET_INTER, {A, C});
    Term intersectionBC = slv.mkTerm(SET_INTER, {B, C});
    Term rhs = slv.mkTerm(SET_UNION, {intersectionAC, intersectionBC});

    Term theorem = slv.mkTerm(EQUAL, {lhs, rhs});

    cout << "cvc5 reports: " << theorem << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
  }

  // Verify emptset is a subset of any set
  {
    Term A = slv.mkConst(set, "A");
    Term emptyset = slv.mkEmptySet(set);

    Term theorem = slv.mkTerm(SET_SUBSET, {emptyset, A});

    cout << "cvc5 reports: " << theorem << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
  }

  // Find me an element in {1, 2} intersection {2, 3}, if there is one.
  {
    Term one = slv.mkInteger(1);
    Term two = slv.mkInteger(2);
    Term three = slv.mkInteger(3);

    Term singleton_one = slv.mkTerm(SET_SINGLETON, {one});
    Term singleton_two = slv.mkTerm(SET_SINGLETON, {two});
    Term singleton_three = slv.mkTerm(SET_SINGLETON, {three});
    Term one_two = slv.mkTerm(SET_UNION, {singleton_one, singleton_two});
    Term two_three = slv.mkTerm(SET_UNION, {singleton_two, singleton_three});
    Term intersection = slv.mkTerm(SET_INTER, {one_two, two_three});

    Term x = slv.mkConst(integer, "x");

    Term e = slv.mkTerm(SET_MEMBER, {x, intersection});

    Result result = slv.checkSatAssuming(e);
    cout << "cvc5 reports: " << e << " is " << result << "." << endl;

    if (result.isSat())
    {
      cout << "For instance, " << slv.getValue(x) << " is a member." << endl;
    }
  }
}
