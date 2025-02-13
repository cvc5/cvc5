/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #308.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("check-proofs", "true");
  Sort s1 = tm.getBooleanSort();
  Term t1 = tm.mkConst(s1, "_x0");
  Term t2 = tm.mkTerm(Kind::XOR, {t1, t1});
  solver.checkSatAssuming({t2});
  auto unsat_core = solver.getUnsatCore();
  assert(!unsat_core.empty());
}
