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
 * Test for project issue #440.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setLogic("QF_ALL");
  solver.setOption("global-negate", "true");
  solver.setOption("produce-unsat-cores", "true");
  Term t9 = tm.mkBoolean(true);
  Term t109 = tm.mkTerm(Kind::NOT, {t9});
  // should throw an option exception
  try
  {
    solver.checkSatAssuming({t109});
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
