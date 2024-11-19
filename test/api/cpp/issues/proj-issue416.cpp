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
 * Test for project issue #416.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("solve-bv-as-int", "sum");
  solver.setOption("strings-exp", "true");
  Sort s1 = tm.getStringSort();
  Term t27 = tm.mkConst(s1, "_x50");
  Term t333 = tm.mkRegexpAll();
  Term t1243 = tm.mkTerm(Kind::STRING_REPLACE_RE_ALL, {t27, t333, t27});
  Term t1291 = tm.mkTerm(Kind::EQUAL, {t1243, t27});
  solver.assertFormula(t1291);
  solver.checkSat();
}
