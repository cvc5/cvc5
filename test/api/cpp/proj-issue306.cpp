/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Solver slv;
  slv.setOption("check-proofs", "true");
  slv.setOption("proof-check", "eager");
  Sort s1 = slv.getBooleanSort();
  Sort s3 = slv.getStringSort();
  Term t1 = slv.mkConst(s3, "_x0");
  Term t3 = slv.mkConst(s1, "_x2");
  Term t11 = slv.mkString("");
  Term t14 = slv.mkConst(s3, "_x11");
  Term t42 = slv.mkTerm(Kind::ITE, {t3, t14, t1});
  Term t58 = slv.mkTerm(Kind::STRING_LEQ, {t14, t11});
  Term t95 = slv.mkTerm(Kind::EQUAL, {t14, t42});
  slv.assertFormula(t95);
  slv.checkSatAssuming({t58});
}
