/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #5074
 */

#include "api/cpp/cvc5.h"

using namespace cvc5::api;

int main()
{
  Solver slv;
  Term c1 = slv.mkConst(slv.getIntegerSort());
  Term t6 = slv.mkTerm(Kind::STRING_FROM_CODE, c1);
  Term t12 = slv.mkTerm(Kind::STRING_TO_REGEXP, t6);
  Term t14 = slv.mkTerm(Kind::STRING_REPLACE_RE, {t6, t12, t6});
  Term t16 = slv.mkTerm(Kind::STRING_CONTAINS, {t14, t14});
  slv.checkEntailed(t16);

  return 0;
}
