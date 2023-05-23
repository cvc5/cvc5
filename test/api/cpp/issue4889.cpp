/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #4889
 */

#include <cvc5/cvc5.h>

using namespace cvc5;

int main()
{
  Solver slv;
  Sort sort_int = slv.getIntegerSort();
  Sort sort_array = slv.mkArraySort(sort_int, sort_int);
  Sort sort_fp128 = slv.mkFloatingPointSort(15, 113);
  Sort sort_fp32 = slv.mkFloatingPointSort(8, 24);
  Sort sort_bool = slv.getBooleanSort();
  Term const0 = slv.mkConst(sort_fp32, "_c0");
  Term const1 = slv.mkConst(sort_fp32, "_c2");
  Term const2 = slv.mkConst(sort_bool, "_c4");
  Term ite = slv.mkTerm(ITE, {const2, const1, const0});
  Term rem = slv.mkTerm(FLOATINGPOINT_REM, {ite, const1});
  Term isnan = slv.mkTerm(FLOATINGPOINT_IS_NAN, {rem});
  slv.checkSatAssuming(isnan);
  return 0;
}
