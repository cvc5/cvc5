/*********************                                                        */
/*! \file simple_vc_quant_cxx.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the C++ interface for quantifiers
 **
 ** A simple demonstration of the C++ interface for quantifiers. 
 **/

#include <iostream>

#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);

  // Prove that the following is unsatisfiable:
  //   forall x. P( x ) ^ ~P( 5 )

  Type integer = em.integerType();
  Type boolean = em.booleanType();
  Type integerPredicate = em.mkFunctionType(integer, boolean);
  
  Expr p = em.mkVar("P", integerPredicate);
  Expr x = em.mkBoundVar("x", integer);
  
  // make forall x. P( x )
  Expr var_list = em.mkExpr(kind::BOUND_VAR_LIST, x);
  Expr px = em.mkExpr(kind::APPLY_UF, p, x);
  Expr quantpospx = em.mkExpr(kind::FORALL, var_list, px);
  cout << "Made expression : " << quantpospx << endl;
  
  //make ~P( 5 )
  Expr five = em.mkConst(Rational(5));
  Expr pfive = em.mkExpr(kind::APPLY_UF, p, five);
  Expr negpfive = em.mkExpr(kind::NOT, pfive);
  cout << "Made expression : " << negpfive << endl;
  
  Expr formula = em.mkExpr(kind::AND, quantpospx, negpfive);

  smt.assertFormula(formula);

  cout << "Checking SAT after asserting " << formula << " to CVC4." << endl;
  cout << "CVC4 should report unsat." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat() << endl;


  SmtEngine smtp(&em);
  
  // this version has a pattern e.g. in smt2 syntax (forall ((x Int)) (! (P x ) :pattern ((P x))))
  Expr pattern = em.mkExpr(kind::INST_PATTERN, px);
  Expr pattern_list = em.mkExpr(kind::INST_PATTERN_LIST, pattern);
  Expr quantpospx_pattern = em.mkExpr(kind::FORALL, var_list, px, pattern_list);
  cout << "Made expression : " << quantpospx_pattern << endl;

  Expr formula_pattern = em.mkExpr(kind::AND, quantpospx_pattern, negpfive);

  smtp.assertFormula(formula_pattern);

  cout << "Checking SAT after asserting " << formula_pattern << " to CVC4." << endl;
  cout << "CVC4 should report unsat." << endl;
  cout << "Result from CVC4 is: " << smtp.checkSat() << endl;


  return 0;
}
