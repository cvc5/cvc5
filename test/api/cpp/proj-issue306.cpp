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
 * Test for project issue #306
 *
 */

#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver slv(tm);
  slv.setOption("check-proofs", "true");
  slv.setOption("proof-check", "eager");
  Sort s1 = tm.getBooleanSort();
  Sort s3 = tm.getStringSort();
  Term t1 = tm.mkConst(s3, "_x0");
  Term t3 = tm.mkConst(s1, "_x2");
  Term t11 = tm.mkString("");
  Term t14 = tm.mkConst(s3, "_x11");
  Term t42 = tm.mkTerm(Kind::ITE, {t3, t14, t1});
  Term t58 = tm.mkTerm(Kind::STRING_LEQ, {t14, t11});
  Term t95 = tm.mkTerm(Kind::EQUAL, {t14, t42});
  slv.assertFormula(t95);
  slv.checkSatAssuming({t58});
}
