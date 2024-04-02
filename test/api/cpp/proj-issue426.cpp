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
 * Test for project issue #426.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setLogic("ALL");
  solver.setOption("strings-exp", "true");
  solver.setOption("produce-models", "true");
  solver.setOption("produce-assertions", "true");
  Sort s1 = tm.getRealSort();
  Sort s2 = tm.getRoundingModeSort();
  Sort s4 = tm.mkSequenceSort(s1);
  Sort s5 = tm.mkArraySort(s4, s4);
  Term t4 = tm.mkConst(s1, "_x3");
  Term t5 = tm.mkReal("9192/832927743");
  Term t19 = tm.mkConst(s2, "_x42");
  Term t24 = tm.mkConst(s5, "_x44");
  Term t37 = tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE);
  solver.checkSat();
  solver.blockModelValues({t24, t19, t4, t37});
  solver.checkSat();
  solver.getValue({t5});
}
