/*********************                                                        */
/*! \file sets-new.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reasoning about sets with CVC4.
 **
 ** A simple demonstration of reasoning about sets with CVC4.
 **/

#include <iostream>

#include <cvc4/api/cvc4cpp.h>

using namespace std;
using namespace CVC4::api;

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

    Term unionAB = slv.mkTerm(UNION, A, B);
    Term lhs = slv.mkTerm(INTERSECTION, unionAB, C);

    Term intersectionAC = slv.mkTerm(INTERSECTION, A, C);
    Term intersectionBC = slv.mkTerm(INTERSECTION, B, C);
    Term rhs = slv.mkTerm(UNION, intersectionAC, intersectionBC);

    Term theorem = slv.mkTerm(EQUAL, lhs, rhs);

    cout << "CVC4 reports: " << theorem << " is "
         << slv.checkValidAssuming(theorem) << "." << endl;
  }

  // Verify emptset is a subset of any set
  {
    Term A = slv.mkConst(set, "A");
    Term emptyset = slv.mkEmptySet(set);

    Term theorem = slv.mkTerm(SUBSET, emptyset, A);

    cout << "CVC4 reports: " << theorem << " is "
         << slv.checkValidAssuming(theorem) << "." << endl;
  }

  // Find me an element in {1, 2} intersection {2, 3}, if there is one.
  {
    Term one = slv.mkReal(1);
    Term two = slv.mkReal(2);
    Term three = slv.mkReal(3);

    Term singleton_one = slv.mkTerm(SINGLETON, one);
    Term singleton_two = slv.mkTerm(SINGLETON, two);
    Term singleton_three = slv.mkTerm(SINGLETON, three);
    Term one_two = slv.mkTerm(UNION, singleton_one, singleton_two);
    Term two_three = slv.mkTerm(UNION, singleton_two, singleton_three);
    Term intersection = slv.mkTerm(INTERSECTION, one_two, two_three);

    Term x = slv.mkConst(integer, "x");

    Term e = slv.mkTerm(MEMBER, x, intersection);

    Result result = slv.checkSatAssuming(e);
    cout << "CVC4 reports: " << e << " is " << result << "." << endl;

    if (result.isSat())
    {
      cout << "For instance, " << slv.getValue(x) << " is a member." << endl;
    }
  }
}
