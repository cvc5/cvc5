/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #576
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("check-abducts", "true");
  solver.setOption("cegis-sample", "trust");
  solver.setOption("produce-abducts", "true");
  Sort s0 = tm.getBooleanSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = solver.getAbduct(t1);

  return 0;
}
