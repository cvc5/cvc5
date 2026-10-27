/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #10104.
 *
 */
#include <cvc5/cvc5.h>

#include <cassert>
#include <string>
#include <vector>

using namespace cvc5;

// Models `steps` steps of the Euclidean algorithm on (a0, b0), where the
// modulo operation is encoded using an existentially quantified quotient.
Result gcd(int a0, int b0, int steps, bool preSkolemQuant)
{
  TermManager tm;
  Solver solver(tm);
  solver.setLogic("NIA");
  if (preSkolemQuant)
  {
    solver.setOption("pre-skolem-quant", "on");
  }
  solver.setOption("produce-models", "true");
  Sort ints = tm.getIntegerSort();
  std::vector<Term> vars;
  vars.push_back(tm.mkConst(ints, "a0"));
  vars.push_back(tm.mkConst(ints, "b0"));
  for (int i = 1; i <= steps; i++)
  {
    vars.push_back(tm.mkConst(ints, "r" + std::to_string(i)));
  }
  solver.assertFormula(vars[0].eqTerm(tm.mkInteger(a0)));
  solver.assertFormula(vars[1].eqTerm(tm.mkInteger(b0)));
  Term q = tm.mkVar(ints, "q");
  Term qlist = tm.mkTerm(Kind::VARIABLE_LIST, {q});
  for (size_t i = 2; i < vars.size(); i++)
  {
    solver.assertFormula(tm.mkTerm(Kind::GEQ, {vars[i], tm.mkInteger(0)}));
    solver.assertFormula(tm.mkTerm(Kind::LT, {vars[i], vars[i - 1]}));
    Term sum = tm.mkTerm(Kind::ADD,
                         {vars[i], tm.mkTerm(Kind::MULT, {vars[i - 1], q})});
    solver.assertFormula(
        tm.mkTerm(Kind::EXISTS, {qlist, sum.eqTerm(vars[i - 2])}));
  }
  Result res = solver.checkSat();
  if (res.isSat())
  {
    for (const Term& v : vars)
    {
      solver.getValue(v);
    }
  }
  return res;
}

int main(void)
{
  // gcd(12,9) = gcd(9,3) = gcd(3,0), so a third step is impossible
  assert(gcd(12, 9, 3, false).isUnsat());
  assert(gcd(12, 9, 3, true).isUnsat());
  // gcd(13,9) = gcd(9,4) = gcd(4,1) = gcd(1,0)
  assert(gcd(13, 9, 3, false).isSat());
  assert(gcd(13, 9, 3, true).isSat());
  return 0;
}
