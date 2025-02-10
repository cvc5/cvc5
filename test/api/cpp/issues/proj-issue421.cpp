/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #421
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_ALL");
  Sort s1 = tm.mkBitVectorSort(4);
  Sort s4 = tm.getRealSort();
  Sort s5 = tm.mkSequenceSort(s1);
  Term t8 = tm.mkConst(s5, "_x49");
  Term t10 = tm.mkConst(s4, "_x51");
  Term t65 = tm.mkTerm(Kind::SEQ_REV, {t8});
  Term t69 = tm.mkTerm(Kind::TANGENT, {t10});
  Term t77 = tm.mkTerm(Kind::LEQ, {t69, t10});
  Term t128 = tm.mkTerm(Kind::SEQ_PREFIX, {t65, t8});
  slv.assertFormula({t77});
  slv.checkSatAssuming(t128.notTerm());
}
