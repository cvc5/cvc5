/*********************                                                        */
/*! \file combination.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the capabilities of CVC4
 **
 ** A simple demonstration of how to use uninterpreted functions, combining this
 ** with arithmetic, and extracting a model at the end of a satisfiable query.
 ** The model is displayed using getValue().
 **/

#include <iostream>

#include <cvc4/api/cvc4cpp.h>

using namespace std;
using namespace CVC4::api;

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
  Solver slv;
  slv.setOption("produce-models", "true");  // Produce Models
  slv.setOption("output-language", "cvc4"); // Set the output-language to CVC's
  slv.setOption("dag-thresh", "0"); // Disable dagifying the output
  slv.setOption("output-language", "smt2"); // use smt-lib v2 as output language
  slv.setLogic(string("QF_UFLIRA"));

  // Sorts
  Sort u = slv.mkUninterpretedSort("u");
  Sort integer = slv.getIntegerSort();
  Sort boolean = slv.getBooleanSort();
  Sort uToInt = slv.mkFunctionSort(u, integer);
  Sort intPred = slv.mkFunctionSort(integer, boolean);

  // Variables
  Term x = slv.mkConst(u, "x");
  Term y = slv.mkConst(u, "y");

  // Functions
  Term f = slv.mkConst(uToInt, "f");
  Term p = slv.mkConst(intPred, "p");

  // Constants
  Term zero = slv.mkReal(0);
  Term one = slv.mkReal(1);

  // Terms
  Term f_x = slv.mkTerm(APPLY_UF, f, x);
  Term f_y = slv.mkTerm(APPLY_UF, f, y);
  Term sum = slv.mkTerm(PLUS, f_x, f_y);
  Term p_0 = slv.mkTerm(APPLY_UF, p, zero);
  Term p_f_y = slv.mkTerm(APPLY_UF, p, f_y);

  // Construct the assertions
  Term assertions = slv.mkTerm(AND,
      vector<Term>{
      slv.mkTerm(LEQ, zero, f_x),  // 0 <= f(x)
      slv.mkTerm(LEQ, zero, f_y),  // 0 <= f(y)
      slv.mkTerm(LEQ, sum, one),   // f(x) + f(y) <= 1
      p_0.notTerm(),               // not p(0)
      p_f_y                        // p(f(y))
      });
  slv.assertFormula(assertions);

  cout << "Given the following assertions:" << endl
       << assertions << endl << endl;

  cout << "Prove x /= y is entailed. " << endl
       << "CVC4: " << slv.checkEntailed(slv.mkTerm(DISTINCT, x, y)) << "."
       << endl
       << endl;

  cout << "Call checkSat to show that the assertions are satisfiable. "
       << endl
       << "CVC4: "
       << slv.checkSat() << "."<< endl << endl;

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

  cout << endl << endl << "Alternatively, print the model." << endl << endl;

  slv.printModel(cout);

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
