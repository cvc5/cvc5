/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #445
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  Solver slv;
  slv.setOption("strings-exp", "true");
  slv.setOption("sygus-abort-size", "1");
  Sort s1 = slv.mkUninterpretedSort("_u0");
  Sort s5 = slv.mkUninterpretedSort("_u1");
  Sort s6 = slv.mkUninterpretedSort("_u2");
  Sort s7 = slv.mkFunctionSort({s1}, s6);
  Term t7 = slv.mkConst(s7, "_x8");
  Term t13 = slv.mkConst(s5, "_x14");
  Term t15 = slv.mkTerm(Kind::SEQ_UNIT, {t13});
  Term t84 = slv.mkTerm(Kind::SEQ_REV, {t15});
  Term t141 = slv.mkTerm(Kind::SEQ_UNIT, {t84});
  Term t229 = slv.mkTerm(Kind::SEQ_UNIT, {t15});
  Term t279 = slv.mkTerm(Kind::SEQ_REPLACE_ALL, {t141, t229, t141});
  Term t289 = slv.mkTerm(Kind::SEQ_PREFIX, {t279, t229});
  slv.assertFormula({t289});
  // should terminate with an exception indicating we are done enumerating
  // rewrite rules.
  try
  {
    (void)slv.simplify(t7);
  }
  catch (cvc5::CVC5ApiException& e)
  {
  }
}
