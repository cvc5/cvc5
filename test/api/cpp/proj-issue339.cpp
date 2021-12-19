/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #339
 *
 */

#include "api/cpp/cvc5.h"

#include <cassert>

using namespace cvc5::api;

int main(void)
{
//  Solver slv;
//  Sort s4 = slv.getIntegerSort();
//  Term t203 = slv.mkInteger("6135470354240554220207");
//  Term t262 = slv.mkTerm(POW2, t203);
//  Term t536 = slv.mkTerm(slv.mkOp(INT_TO_BITVECTOR, 49), t262);
//  slv.simplify(t536);
//
//
  Solver slv;
  Sort s4 = slv.getIntegerSort();
  Term t203 = slv.mkInteger("6135470354240554220207");
  Term t204 = slv.mkInteger("2");
  Term t262 = slv.mkTerm(POW, t204, t203);
  try {
    slv.simplify(t262);
  } catch (LogicException e) {
    std::cout << "caught the expected exception" << std::endl;
  }
  assert(false);
}
