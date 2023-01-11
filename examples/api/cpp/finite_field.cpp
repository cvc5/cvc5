/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of solving finite field problems with cvc5's cpp API
 */

#include <cvc5/cvc5.h>

#include <cassert>
#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  Solver solver;
  solver.setOption("produce-models", "true");

  Sort f5 = solver.mkFiniteFieldSort("5");
  Term a = solver.mkConst(f5, "a");
  Term b = solver.mkConst(f5, "b");
  Term z = solver.mkFiniteFieldElem("0", f5);

  Term inv =
      solver.mkTerm(EQUAL,
                    {solver.mkTerm(FINITE_FIELD_ADD,
                                   {solver.mkTerm(FINITE_FIELD_MULT, {a, b}),
                                    solver.mkFiniteFieldElem("-1", f5)}),
                     z});
  Term aIsTwo = solver.mkTerm(
      EQUAL,
      {solver.mkTerm(FINITE_FIELD_ADD, {a, solver.mkFiniteFieldElem("-2", f5)}),
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
  Term bIsTwo = solver.mkTerm(
      EQUAL,
      {solver.mkTerm(FINITE_FIELD_ADD, {b, solver.mkFiniteFieldElem("-2", f5)}),
       z});

  // should be UNSAT, 2*2 - 1 != 0
  solver.assertFormula(bIsTwo);

  r = solver.checkSat();
  assert(!r.isSat());
}
