/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #7000
 */

#include "api/cpp/cvc5.h"

using namespace cvc5::api;

int main()
{
  Solver slv;
  Sort s1 = slv.getIntegerSort();
  Sort s2 = slv.mkFunctionSort(s1, s1);
  Sort s3 = slv.getRealSort();
  Term t4 = slv.mkPi();
  Term t7 = slv.mkConst(s3, "_x5");
  Term t37 = slv.mkConst(s2, "_x32");
  Term t59 = slv.mkConst(s2, "_x51");
  Term t72 = slv.mkTerm(EQUAL, t37, t59);
  Term t74 = slv.mkTerm(GT, t4, t7);
  slv.checkEntailed({t72, t74, t72, t72});
  return 0;
}
