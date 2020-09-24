/*********************                                                        */
/*! \file issue4889.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Test for issue #4889
 **/

#include "api/cvc4cpp.h"

using namespace CVC4::api;

int main()
{
#ifdef CVC4_USE_SYMFPU
  Solver slv;
  Sort sort_int = slv.getIntegerSort();
  Sort sort_array = slv.mkArraySort(sort_int, sort_int);
  Sort sort_fp128 = slv.mkFloatingPointSort(15, 113);
  Sort sort_fp32 = slv.mkFloatingPointSort(8, 24);
  Sort sort_bool = slv.getBooleanSort();
  Term const0 = slv.mkConst(sort_fp32, "_c0");
  Term const1 = slv.mkConst(sort_fp32, "_c2");
  Term const2 = slv.mkConst(sort_bool, "_c4");
  Term ite = slv.mkTerm(ITE, const2, const1, const0);
  Term rem = slv.mkTerm(FLOATINGPOINT_REM, ite, const1);
  Term isnan = slv.mkTerm(FLOATINGPOINT_ISNAN, rem);
  slv.checkSatAssuming(isnan);
#endif
  return 0;
}
