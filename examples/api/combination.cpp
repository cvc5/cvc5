/*********************                                                        */
/*! \file combination.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple demonstration of the  capabilities of CVC4
 **
 ** A simple demonstration of how to use uninterpreted functions, combining this
 ** with arithmetic, and extracting a model at the end of a satisfiable query.
 **/

#include <iostream>

//#include <cvc4/cvc4.h> // use this after CVC4 is properly installed
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setOption("tlimit", 100);
  smt.setOption("produce-models", true); // Produce Models
  smt.setOption("incremental", true); // Produce Models
  smt.setOption("output-language", "smtlib"); // output-language

  // Sorts
  SortType u = em.mkSort("u");
  Type integer = em.integerType();
  Type boolean = em.booleanType();
  Type uToInt = em.mkFunctionType(u, integer);
  Type intPred = em.mkFunctionType(integer, boolean);

  // Variables
  Expr x = em.mkVar("x", u);
  Expr y = em.mkVar("y", u);

  //Functions
  Expr f = em.mkVar("f", uToInt);
  Expr p = em.mkVar("p", intPred);

  // Constants
  Expr zero = em.mkConst(Rational(0));
  Expr one = em.mkConst(Rational(1));

  // terms
  Expr f_x = em.mkExpr(kind::APPLY_UF, f, x);
  Expr f_y = em.mkExpr(kind::APPLY_UF, f, y);
  Expr sum = em.mkExpr(kind::PLUS, f_x, f_y);
  Expr p_0 = em.mkExpr(kind::APPLY_UF, p, zero);
  Expr p_f_y = em.mkExpr(kind::APPLY_UF, p, f_y);

  smt.assertFormula(em.mkExpr(kind::LEQ, zero, f_x)); // 0 <= f(x)
  smt.assertFormula(em.mkExpr(kind::LEQ, zero, f_y)); // 0 <= f(y)
  smt.assertFormula(em.mkExpr(kind::LEQ, sum, one));  // f(x) + f(y) <= 1
  smt.assertFormula(p_0.notExpr());                   // not p(0)
  smt.assertFormula(p_f_y);                           // p(f(y))

  cout << "Under the assumptions, prove x cannot equal y is valid: "
       << " CVC4 says " << smt.query(em.mkExpr(kind::DISTINCT, x, y)) << endl;

  cout << "Now we call checksat on a trivial query to show that" << endl
       << "the assumptions are satisfiable: "
       << smt.checkSat(em.mkConst(true)) << "."<< endl;
  cout << smt.getValue(x) << endl;
  cout << smt.getValue(y) << endl;
  cout << smt.getValue(f_x) << endl;
  cout << smt.getValue(f_y) << endl;
  cout << smt.getValue(p_f_y) << endl;
  cout << smt.getValue(p_0) << endl;

  cout << smt.getValue(f) << endl;
  cout << smt.getValue(p) << endl;

  return 0;
}
