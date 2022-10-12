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

#include <cassert>
#include <iostream>

#include "api/cpp/cvc5.h"

using namespace std;
using namespace cvc5;

int main()
{
  Solver solver;
  solver.setOption("produce-models", "true");

  // Make single precision floating-point variables
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
  solver.assertFormula(inv);
  solver.assertFormula(aIsTwo);

  Result r = solver.checkSat();  // result is sat
  assert(r.isSat());

  cout << "a = " << solver.getValue(a) << endl;
  cout << "b = " << solver.getValue(b) << endl;

  Term bIsTwo = solver.mkTerm(
      EQUAL,
      {solver.mkTerm(FINITE_FIELD_ADD, {b, solver.mkFiniteFieldElem("-2", f5)}),
       z});

  solver.assertFormula(bIsTwo);

  r = solver.checkSat();  // result is sat
  assert(!r.isSat());
}
