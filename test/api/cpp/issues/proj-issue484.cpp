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
 * Test for project issue #445
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver slv(tm);
  Sort s1 = tm.getIntegerSort();
  Term t1 = tm.mkVar(s1, "_x0");
  Term t3 = tm.mkInteger("8072314426184292007005683562403");
  Term t7 = tm.mkTerm(Kind::ADD, {t1, t1, t1, t3});
  Term t8 = tm.mkTerm(tm.mkOp(Kind::DIVISIBLE, {2319436191}), {t7});
  Term vl = tm.mkTerm(Kind::VARIABLE_LIST, {t1});
  Term t10 = tm.mkTerm(Kind::FORALL, {vl, t8});
  slv.checkSatAssuming({t10});
  slv.assertFormula({t10});
  slv.checkSat();
}
