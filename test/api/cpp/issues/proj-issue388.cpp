/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #388
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

#include "base/configuration.h"

using namespace cvc5;

int main(void)
{
  if (!internal::Configuration::isBuiltWithPoly())
  {
    return 0;
  }
  {  // Original
    TermManager tm;
    Solver slv(tm);
    slv.setLogic("QF_NRA");
    Sort s = tm.getRealSort();
    Term t1 = tm.mkConst(s, "a");
    Term t2 = tm.mkConst(s, "b");
    Term t3 = tm.mkConst(s, "c");
    Term t4 = tm.mkTerm(Kind::DIVISION, {t1, t2});
    Term t5 = tm.mkTerm(Kind::GT, {t4, t3});
    Term t6 = tm.mkTerm(Kind::DIVISION, {t1, t3});
    Term t7 = tm.mkTerm(Kind::IS_INTEGER, {t6});
    Term t8 = tm.mkTerm(Kind::AND, {t5, t7, t5});
    Term t9 = tm.mkTerm(Kind::NOT, {t8});
    slv.assertFormula(t9);
    slv.checkSat();
  }
  {  // Minimized
    TermManager tm;
    Solver slv(tm);
    slv.setOption("nl-cov", "true");
    slv.setOption("nl-cov-var-elim", "true");
    slv.setOption("nl-ext", "none");
    slv.setLogic("QF_NIRA");
    Sort s = tm.getRealSort();
    Term t1 = tm.mkConst(s, "a");
    Term t2 = tm.mkConst(s, "b");
    Term t3 = tm.mkReal(0);
    Term t7 = tm.mkTerm(Kind::IS_INTEGER, {t1});
    Term t4 = tm.mkTerm(Kind::DIVISION, {t2, t1});
    Term t5 = tm.mkTerm(Kind::DISTINCT, {t3, t4});
    Term t8 = tm.mkTerm(Kind::OR, {t7, t5});
    slv.assertFormula(t8);
    slv.checkSat();
  }
}
