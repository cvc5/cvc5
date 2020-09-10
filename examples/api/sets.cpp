/*********************                                                        */
/*! \file sets.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reasoning about sets with CVC4.
 **
 ** A simple demonstration of reasoning about sets with CVC4.
 **/

#include <iostream>

#include <cvc4/cvc4.h>
#include <cvc4/options/set_language.h>

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);

  // Optionally, set the logic. We need at least UF for equality predicate,
  // integers (LIA) and sets (FS).
  smt.setLogic("QF_UFLIAFS");

  // Produce models
  smt.setOption("produce-models", true);

  // Set output language to SMTLIB2
  cout << language::SetLanguage(language::output::LANG_SMTLIB_V2);

  Type integer = em.integerType();
  Type set = em.mkSetType(integer);

  // Verify union distributions over intersection
  // (A union B) intersection C = (A intersection C) union (B intersection C)
  {
    Expr A = em.mkVar("A", set);
    Expr B = em.mkVar("B", set);
    Expr C = em.mkVar("C", set);

    Expr unionAB = em.mkExpr(kind::UNION, A, B);
    Expr lhs = em.mkExpr(kind::INTERSECTION, unionAB, C);

    Expr intersectionAC = em.mkExpr(kind::INTERSECTION, A, C);
    Expr intersectionBC = em.mkExpr(kind::INTERSECTION, B, C);
    Expr rhs = em.mkExpr(kind::UNION, intersectionAC, intersectionBC);

    Expr theorem = em.mkExpr(kind::EQUAL, lhs, rhs);

    cout << "CVC4 reports: " << theorem << " is " << smt.checkEntailed(theorem)
         << "." << endl;
  }

  // Verify emptset is a subset of any set
  {
    Expr A = em.mkVar("A", set);
    Expr emptyset = em.mkConst(EmptySet(set));

    Expr theorem = em.mkExpr(kind::SUBSET, emptyset, A);

    cout << "CVC4 reports: " << theorem << " is " << smt.checkEntailed(theorem)
         << "." << endl;
  }

  // Find me an element in {1, 2} intersection {2, 3}, if there is one.
  {
    Expr one = em.mkConst(Rational(1));
    Expr two = em.mkConst(Rational(2));
    Expr three = em.mkConst(Rational(3));

    Expr singleton_one = em.mkExpr(kind::SINGLETON, one);
    Expr singleton_two = em.mkExpr(kind::SINGLETON, two);
    Expr singleton_three = em.mkExpr(kind::SINGLETON, three);
    Expr one_two = em.mkExpr(kind::UNION, singleton_one, singleton_two);
    Expr two_three = em.mkExpr(kind::UNION, singleton_two, singleton_three);
    Expr intersection = em.mkExpr(kind::INTERSECTION, one_two, two_three);

    Expr x = em.mkVar("x", integer);

    Expr e = em.mkExpr(kind::MEMBER, x, intersection);

    Result result = smt.checkSat(e);
    cout << "CVC4 reports: " << e << " is " << result << "." << endl;

    if(result == Result::SAT) {
      cout << "For instance, " << smt.getValue(x) << " is a member." << endl;
    }
  }
}
