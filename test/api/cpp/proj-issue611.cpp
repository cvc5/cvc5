/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #611
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("solve-bv-as-int", "bitwise");
  // should throw an exception due to the usage of an illegal value
  // (0) for the option
  try
  {
    solver.setOption("bvand-integer-granularity", "0");
  }
  catch (cvc5::CVC5ApiOptionException& e)
  {
  }
  return 0;
}
