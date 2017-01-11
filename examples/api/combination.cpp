/*********************                                                        */
/*! \file combination.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

//#include <cvc4/cvc4.h> // use this after CVC4 is properly installed
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;

void prefixPrintGetValue(SmtEngine& smt, Expr e, int level = 0){
  for(int i = 0; i < level; ++i){ cout << '-'; }
  cout << "smt.getValue(" << e << ") -> " << smt.getValue(e) << endl;

  if(e.hasOperator() && e.getOperator().getKind() != kind::BUILTIN){
    prefixPrintGetValue(smt, e.getOperator(), level + 1);
  }

  for(Expr::const_iterator term_i = e.begin(), term_end = e.end();
      term_i != term_end; ++term_i)
  {
    Expr curr = *term_i;
    prefixPrintGetValue(smt, curr, level + 1);
  }
}


int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setOption("produce-models", true); // Produce Models
  smt.setOption("output-language", "cvc4"); // Set the output-language to CVC's
  smt.setOption("default-dag-thresh", 0); //Disable dagifying the output
  smt.setLogic(string("QF_UFLIRA"));

  // Sorts
  SortType u = em.mkSort("u");
  Type integer = em.integerType();
  Type boolean = em.booleanType();
  Type uToInt = em.mkFunctionType(u, integer);
  Type intPred = em.mkFunctionType(integer, boolean);

  // Variables
  Expr x = em.mkVar("x", u);
  Expr y = em.mkVar("y", u);

  // Functions
  Expr f = em.mkVar("f", uToInt);
  Expr p = em.mkVar("p", intPred);

  // Constants
  Expr zero = em.mkConst(Rational(0));
  Expr one = em.mkConst(Rational(1));

  // Terms
  Expr f_x = em.mkExpr(kind::APPLY_UF, f, x);
  Expr f_y = em.mkExpr(kind::APPLY_UF, f, y);
  Expr sum = em.mkExpr(kind::PLUS, f_x, f_y);
  Expr p_0 = em.mkExpr(kind::APPLY_UF, p, zero);
  Expr p_f_y = em.mkExpr(kind::APPLY_UF, p, f_y);

  // Construct the assumptions
  Expr assumptions =
    em.mkExpr(kind::AND,
              em.mkExpr(kind::LEQ, zero, f_x), // 0 <= f(x)
              em.mkExpr(kind::LEQ, zero, f_y), // 0 <= f(y)
              em.mkExpr(kind::LEQ, sum, one),  // f(x) + f(y) <= 1
              p_0.notExpr(),                   // not p(0)
              p_f_y);                          // p(f(y))
  smt.assertFormula(assumptions);

  cout << "Given the following assumptions:" << endl
       << assumptions << endl
       << "Prove x /= y is valid. "
       << "CVC4 says: " << smt.query(em.mkExpr(kind::DISTINCT, x, y))
       << "." << endl;

  cout << "Now we call checksat on a trivial query to show that" << endl
       << "the assumptions are satisfiable: "
       << smt.checkSat(em.mkConst(true)) << "."<< endl;

  cout << "Finally, after a SAT call, we recursively call smt.getValue(...) on "
       << "all of the assumptions to see what the satisfying model looks like."
       << endl;
  prefixPrintGetValue(smt, assumptions);

  return 0;
}
