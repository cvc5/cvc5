/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the capabilities of cvc5
 *
 * A simple demonstration of how to use uninterpreted functions, combining this
 * with arithmetic, and extracting a model at the end of a satisfiable query.
 * The model is displayed using getValue().
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
  slv.setOption("produce-models", "true");  // Produce Models
  slv.setOption("dag-thresh", "0"); // Disable dagifying the output
  slv.setLogic("QF_UFLIRA");

  // Sorts
  Sort u = tm.mkUninterpretedSort("u");
  Sort integer = tm.getIntegerSort();
  Sort boolean = tm.getBooleanSort();
  Sort uToInt = tm.mkFunctionSort({u}, integer);
  Sort intPred = tm.mkFunctionSort({integer}, boolean);

  // Variables
  Term x = tm.mkConst(u, "x");
  Term y = tm.mkConst(u, "y");

  // Functions
  Term f = tm.mkConst(uToInt, "f");
  Term p = tm.mkConst(intPred, "p");

  // Constants
  Term zero = tm.mkInteger(0);
  Term one = tm.mkInteger(1);

  // Terms
  Term f_x = tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term sum = tm.mkTerm(Kind::ADD, {f_x, f_y});
  Term p_0 = tm.mkTerm(Kind::APPLY_UF, {p, zero});
  Term p_f_y = tm.mkTerm(Kind::APPLY_UF, {p, f_y});

  // Construct the assertions
  Term assertions =
      tm.mkTerm(Kind::AND,
                {
                    tm.mkTerm(Kind::LEQ, {zero, f_x}),  // 0 <= f(x)
                    tm.mkTerm(Kind::LEQ, {zero, f_y}),  // 0 <= f(y)
                    tm.mkTerm(Kind::LEQ, {sum, one}),   // f(x) + f(y) <= 1
                    p_0.notTerm(),                      // not p(0)
                    p_f_y                               // p(f(y))
                });
  slv.assertFormula(assertions);

  cout << "Given the following assertions:" << endl
       << assertions << endl << endl;

  cout << "Prove x /= y is entailed." << endl
       << "cvc5: " << slv.checkSatAssuming(tm.mkTerm(Kind::EQUAL, {x, y}))
       << "." << endl
       << endl;

  cout << "Call checkSat to show that the assertions are satisfiable." << endl
       << "cvc5: " << slv.checkSat() << "." << endl
       << endl;

  cout << "Call slv.getValue(...) on terms of interest."
       << endl;
  cout << "slv.getValue(" << f_x << "): " << slv.getValue(f_x) << endl;
  cout << "slv.getValue(" << f_y << "): " << slv.getValue(f_y) << endl;
  cout << "slv.getValue(" << sum << "): " << slv.getValue(sum) << endl;
  cout << "slv.getValue(" << p_0 << "): " << slv.getValue(p_0) << endl;
  cout << "slv.getValue(" << p_f_y << "): " << slv.getValue(p_f_y)
       << endl << endl;

  cout << "Alternatively, iterate over assertions and call slv.getValue(...) "
       << "on all terms."
       << endl;
  prefixPrintGetValue(slv, assertions);

  cout << endl;
  cout << "You can also use nested loops to iterate over terms." << endl;
  for (Term::const_iterator it = assertions.begin();
       it != assertions.end();
       ++it)
  {
    cout << "term: " << *it << endl;
    for (Term::const_iterator it2 = (*it).begin();
         it2 != (*it).end();
         ++it2)
    {
      cout << " + child: " << *it2 << std::endl;
    }
  }
  cout << endl;
  cout << "Alternatively, you can also use for-each loops." << endl;
  for (const Term& t : assertions)
  {
    cout << "term: " << t << endl;
    for (const Term& c : t)
    {
      cout << " + child: " << c << endl;
    }
  }

  return 0;
}
