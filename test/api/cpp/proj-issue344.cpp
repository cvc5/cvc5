/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Yoni Zohar, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #345
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver slv(tm);
  slv.setOption("solve-bv-as-int", "iand");
  Sort s12 = tm.getIntegerSort();
  Term t13 = tm.mkConst(s12, "_x11");
  Term t25 = tm.mkTerm(tm.mkOp(Kind::INT_TO_BITVECTOR, {4124876294}), {t13});
  Term t66 = tm.mkTerm(Kind::BITVECTOR_ULTBV, {t25, t25});
  Term t154 = tm.mkTerm(Kind::BITVECTOR_SGT, {t66, t66});
  Term query = tm.mkTerm(Kind::AND, {t154, t154, t154, t154});
  slv.checkSatAssuming(query.notTerm());
}
