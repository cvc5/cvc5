/*********************                                                        */
/*! \file extract.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the solving capabilities of the CVC4
 ** bit-vector solver.
 **
 **/

#include <iostream>

#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setLogic("QF_BV"); // Set the logic

  Type bitvector32 = em.mkBitVectorType(32);

  Expr x = em.mkVar("a", bitvector32);

  Expr ext_31_1 = em.mkConst(CVC4::BitVectorExtract(31,1));
  Expr x_31_1 = em.mkExpr(ext_31_1, x);

  Expr ext_30_0 = em.mkConst(CVC4::BitVectorExtract(30,0));
  Expr x_30_0 = em.mkExpr(ext_30_0, x);

  Expr ext_31_31 = em.mkConst(CVC4::BitVectorExtract(31,31));
  Expr x_31_31 = em.mkExpr(ext_31_31, x);

  Expr ext_0_0 = em.mkConst(CVC4::BitVectorExtract(0,0));
  Expr x_0_0 = em.mkExpr(ext_0_0, x);

  Expr eq = em.mkExpr(kind::EQUAL, x_31_1, x_30_0);
  cout << " Asserting: " << eq << endl;
  smt.assertFormula(eq);

  Expr eq2 = em.mkExpr(kind::EQUAL, x_31_31, x_0_0);
  cout << " Querying: " << eq2 << endl;
  cout << " Expect entailed. " << endl;
  cout << " CVC4: " << smt.checkEntailed(eq2) << endl;

  return 0;
}
