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

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5::api;

int main(void)
{
  Sort s4 = d_solver.getIntegerSort();
  Term t203 = d_solver.mkInteger("6135470354240554220207");
  Term t262 = d_solver.mkTerm(POW2, t203);
  Term t536 = d_solver.mkTerm(d_solver.mkOp(INT_TO_BITVECTOR, 49), t262);
  d_solver.simplify(t536);
}
