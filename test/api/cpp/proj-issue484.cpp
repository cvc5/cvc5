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
 * Test for project issue #445
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  Solver slv;
  Sort s1 = slv.getIntegerSort();
  Term t1 = slv.mkVar(s1, "_x0");
  Term t3 = slv.mkInteger("8072314426184292007005683562403");
  Term t7 = slv.mkTerm(Kind::ADD, {t1, t1, t1, t3});
  Term t8 = slv.mkTerm(slv.mkOp(Kind::DIVISIBLE, {2319436191}), {t7});
  Term vl = slv.mkTerm(Kind::VARIABLE_LIST, {t1});
  Term t10 = slv.mkTerm(Kind::FORALL, {vl, t8});
  slv.checkSatAssuming({t10});
  slv.assertFormula({t10});
  slv.checkSat();
}
