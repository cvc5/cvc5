/*********************                                                        */
/*! \file extract-new.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the solving capabilities of the CVC4
 ** bit-vector solver.
 **
 **/

#include <iostream>

#include <cvc4/api/cvc4cpp.h>

using namespace std;
using namespace CVC4::api;

int main()
{
  Solver slv;
  slv.setLogic("QF_BV"); // Set the logic

  Sort bitvector32 = slv.mkBitVectorSort(32);

  Term x = slv.mkConst(bitvector32, "a");

  OpTerm ext_31_1 = slv.mkOpTerm(BITVECTOR_EXTRACT_OP, 31, 1);
  Term x_31_1 = slv.mkTerm(BITVECTOR_EXTRACT, ext_31_1, x);

  OpTerm ext_30_0 = slv.mkOpTerm(BITVECTOR_EXTRACT_OP, 30, 0);
  Term x_30_0 = slv.mkTerm(BITVECTOR_EXTRACT, ext_30_0, x);

  OpTerm ext_31_31 = slv.mkOpTerm(BITVECTOR_EXTRACT_OP, 31, 31);
  Term x_31_31 = slv.mkTerm(BITVECTOR_EXTRACT, ext_31_31, x);

  OpTerm ext_0_0 = slv.mkOpTerm(BITVECTOR_EXTRACT_OP, 0, 0);
  Term x_0_0 = slv.mkTerm(BITVECTOR_EXTRACT, ext_0_0, x);

  Term eq = slv.mkTerm(EQUAL, x_31_1, x_30_0);
  cout << " Asserting: " << eq << endl;
  slv.assertFormula(eq);

  Term eq2 = slv.mkTerm(EQUAL, x_31_31, x_0_0);
  cout << " Check validity assuming: " << eq2 << endl;
  cout << " Expect valid. " << endl;
  cout << " CVC4: " << slv.checkValidAssuming(eq2) << endl;

  return 0;
}
