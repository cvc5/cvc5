/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Kshitij Bansal, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about sets via the C++ API.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);

  // Optionally, set the logic. We need at least UF for equality predicate,
  // integers (LIA) and sets (FS).
  slv.setLogic("QF_UFLIAFS");

  // Produce models
  slv.setOption("produce-models", "true");

  Sort integer = tm.getIntegerSort();
  Sort set = tm.mkSetSort(integer);

  // Verify union distributions over intersection
  // (A union B) intersection C = (A intersection C) union (B intersection C)
  {
    Term A = tm.mkConst(set, "A");
    Term B = tm.mkConst(set, "B");
    Term C = tm.mkConst(set, "C");

    Term unionAB = tm.mkTerm(Kind::SET_UNION, {A, B});
    Term lhs = tm.mkTerm(Kind::SET_INTER, {unionAB, C});

    Term intersectionAC = tm.mkTerm(Kind::SET_INTER, {A, C});
    Term intersectionBC = tm.mkTerm(Kind::SET_INTER, {B, C});
    Term rhs = tm.mkTerm(Kind::SET_UNION, {intersectionAC, intersectionBC});

    Term theorem = tm.mkTerm(Kind::EQUAL, {lhs, rhs});

    cout << "cvc5 reports: " << theorem << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
  }

  // Verify emptset is a subset of any set
  {
    Term A = tm.mkConst(set, "A");
    Term emptyset = tm.mkEmptySet(set);

    Term theorem = tm.mkTerm(Kind::SET_SUBSET, {emptyset, A});

    cout << "cvc5 reports: " << theorem << " is "
         << slv.checkSatAssuming(theorem.notTerm()) << "." << endl;
  }

  // Find me an element in {1, 2} intersection {2, 3}, if there is one.
  {
    Term one = tm.mkInteger(1);
    Term two = tm.mkInteger(2);
    Term three = tm.mkInteger(3);

    Term singleton_one = tm.mkTerm(Kind::SET_SINGLETON, {one});
    Term singleton_two = tm.mkTerm(Kind::SET_SINGLETON, {two});
    Term singleton_three = tm.mkTerm(Kind::SET_SINGLETON, {three});
    Term one_two = tm.mkTerm(Kind::SET_UNION, {singleton_one, singleton_two});
    Term two_three =
        tm.mkTerm(Kind::SET_UNION, {singleton_two, singleton_three});
    Term intersection = tm.mkTerm(Kind::SET_INTER, {one_two, two_three});

    Term x = tm.mkConst(integer, "x");

    Term e = tm.mkTerm(Kind::SET_MEMBER, {x, intersection});

    Result result = slv.checkSatAssuming(e);
    cout << "cvc5 reports: " << e << " is " << result << "." << endl;

    if (result.isSat())
    {
      cout << "For instance, " << slv.getValue(x) << " is a member." << endl;
    }
  }
}
