/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #5074
 */

#include <cvc5/cvc5.h>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);
  Term c1 = tm.mkConst(tm.getIntegerSort());
  Term t6 = tm.mkTerm(Kind::STRING_FROM_CODE, {c1});
  Term t12 = tm.mkTerm(Kind::STRING_TO_REGEXP, {t6});
  Term t14 = tm.mkTerm(Kind::STRING_REPLACE_RE, {t6, t12, t6});
  Term t16 = tm.mkTerm(Kind::STRING_CONTAINS, {t14, t14});
  slv.checkSatAssuming(t16.notTerm());

  return 0;
}
