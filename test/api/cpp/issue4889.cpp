/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Solver slv(tm);
  Sort sort_int = tm.getIntegerSort();
  Sort sort_array = tm.mkArraySort(sort_int, sort_int);
  Sort sort_fp128 = tm.mkFloatingPointSort(15, 113);
  Sort sort_fp32 = tm.mkFloatingPointSort(8, 24);
  Sort sort_bool = tm.getBooleanSort();
  Term const0 = tm.mkConst(sort_fp32, "_c0");
  Term const1 = tm.mkConst(sort_fp32, "_c2");
  Term const2 = tm.mkConst(sort_bool, "_c4");
  Term ite = tm.mkTerm(Kind::ITE, {const2, const1, const0});
  Term rem = tm.mkTerm(Kind::FLOATINGPOINT_REM, {ite, const1});
  Term isnan = tm.mkTerm(Kind::FLOATINGPOINT_IS_NAN, {rem});
  slv.checkSatAssuming(isnan);
  return 0;
}
