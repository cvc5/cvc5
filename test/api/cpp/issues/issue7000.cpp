/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #7000.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);
  Sort s1 = tm.getIntegerSort();
  Sort s2 = tm.mkFunctionSort({s1}, s1);
  Sort s3 = tm.getRealSort();
  Term t4 = tm.mkPi();
  Term t7 = tm.mkConst(s3, "_x5");
  Term t37 = tm.mkConst(s2, "_x32");
  Term t59 = tm.mkConst(s2, "_x51");
  Term t72 = tm.mkTerm(Kind::EQUAL, {t37, t59});
  Term t74 = tm.mkTerm(Kind::GT, {t4, t7});
  Term query = tm.mkTerm(Kind::AND, {t72, t74, t72, t72});
  // throws logic exception since logic is not higher order by default
  try
  {
    solver.checkSatAssuming(query.notTerm());
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
