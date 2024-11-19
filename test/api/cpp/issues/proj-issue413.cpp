/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #413.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("produce-models", "true");
  solver.setOption("produce-unsat-assumptions", "true");
  solver.setOption("produce-assertions", "true");
  Sort s1 = tm.getStringSort();
  Sort s3 = tm.getIntegerSort();
  Sort s7 = tm.mkArraySort(s1, s3);
  Term t3 = tm.mkConst(s1, "_x2");
  Term t57 = tm.mkVar(s7, "_x38");
  Term t103 = tm.mkTerm(Kind::SELECT, {t57, t3});
  solver.checkSat();
  try
  {
    solver.blockModelValues({t103});
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
