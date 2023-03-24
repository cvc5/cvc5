/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("check-abducts", "true");
  solver.setOption("cegis-sample", "trust");
  solver.setOption("produce-abducts", "true");
  Sort s0 = solver.getBooleanSort();
  Term t1 = solver.mkConst(s0, "_x0");
  Term t2 = solver.getAbduct(t1);

  return 0;
}
