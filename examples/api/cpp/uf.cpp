/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the capabilities of cvc5 uf solver.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5;

void prefixPrintGetValue(Solver& slv, Term t, int level = 0)
{
  cout << "slv.getValue(" << t << "): " << slv.getValue(t) << endl;

  for (const Term& c : t)
  {
    prefixPrintGetValue(slv, c, level + 1);
  }
}

int main()
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic(string("QF_UF"));

  // Sorts
  Sort u = tm.mkUninterpretedSort("u");
  Sort boolean = tm.getBooleanSort();
  Sort uTou = tm.mkFunctionSort({u}, u);
  Sort uPred = tm.mkFunctionSort({u}, boolean);

  // Variables
  Term x = tm.mkConst(u, "x");
  Term y = tm.mkConst(u, "y");

  // Functions
  Term f = tm.mkConst(uTou, "f");
  Term p = tm.mkConst(uPred, "p");

  // Terms
  Term f_x = tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term p_f_x = tm.mkTerm(Kind::APPLY_UF, {p, f_x});
  Term p_f_y = tm.mkTerm(Kind::APPLY_UF, {p, f_y});

  // Construct the assertions
  Term assertions =
      tm.mkTerm(Kind::AND,
                {
                    tm.mkTerm(Kind::EQUAL, {x, f_x}),  
                    tm.mkTerm(Kind::EQUAL, {y, f_y}),
                    p_f_x.notTerm(),
                    p_f_y
                });
  slv.assertFormula(assertions);

  std::cout << slv.checkSat()  << std::endl;

  return 0;
}
