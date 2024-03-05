/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of solving finite field problems with cvc5's cpp API.
 */

#include <cvc5/cvc5.h>

#include <cassert>
#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("produce-models", "true");

  Sort f5 = tm.mkFiniteFieldSort("5");
  Term a = tm.mkConst(f5, "a");
  Term b = tm.mkConst(f5, "b");
  Term z = tm.mkFiniteFieldElem("0", f5);

  Term inv = tm.mkTerm(Kind::EQUAL,
                       {tm.mkTerm(Kind::FINITE_FIELD_ADD,
                                  {tm.mkTerm(Kind::FINITE_FIELD_MULT, {a, b}),
                                   tm.mkFiniteFieldElem("-1", f5)}),
                        z});
  Term aIsTwo = tm.mkTerm(
      Kind::EQUAL,
      {tm.mkTerm(Kind::FINITE_FIELD_ADD, {a, tm.mkFiniteFieldElem("-2", f5)}),
       z});
  // ab - 1 = 0
  solver.assertFormula(inv);
  // a = 2
  solver.assertFormula(aIsTwo);

  // should be SAT, with b = 2^(-1)
  Result r = solver.checkSat();
  assert(r.isSat());

  cout << "a = " << solver.getValue(a) << endl;
  cout << "b = " << solver.getValue(b) << endl;

  // b = 2
  Term bIsTwo = tm.mkTerm(
      Kind::EQUAL,
      {tm.mkTerm(Kind::FINITE_FIELD_ADD, {b, tm.mkFiniteFieldElem("-2", f5)}),
       z});

  // should be UNSAT, 2*2 - 1 != 0
  solver.assertFormula(bIsTwo);

  r = solver.checkSat();
  assert(!r.isSat());
}
