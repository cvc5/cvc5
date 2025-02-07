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
 * Test for project issue #414.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  Sort s2 = tm.getRealSort();
  Term t1 = tm.mkConst(s2, "_x0");
  Term t16 = tm.mkTerm(Kind::PI);
  Term t53 = tm.mkTerm(Kind::SUB, {t1, t16});
  Term t54 = tm.mkTerm(Kind::SECANT, {t53});
  solver.simplify(t54);
}
