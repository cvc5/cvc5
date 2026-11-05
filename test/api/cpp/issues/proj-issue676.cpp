/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #676
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("incremental", "false");
  solver.setLogic("ALL");
  solver.setOption("check-models", "true");
  solver.setOption("sets-exp", "true");
  solver.setOption("strings-exp", "true");
  solver.setOption("fmf-bound", "true");
  solver.setOption("debug-check-models", "true");
  solver.setOption("produce-unsat-assumptions", "true");
  solver.setOption("trigger-active-sel", "max");
  solver.setOption("produce-models", "true");
  Sort s0 = tm.getRealSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = tm.mkVar(s0, "_x5");
  Term t3 = tm.mkVar(s0, "_x6");
  Sort s4 = tm.mkSequenceSort(s0);
  Sort s5 = tm.mkBagSort(s4);
  Term t6 = tm.mkConst(s5, "_x10");
  Term t7 = tm.mkConst(s5, "_x11");
  Term t8 = tm.mkEmptySequence(s0);
  Term t9 = tm.mkTerm(Kind::BAG_DIFFERENCE_SUBTRACT, {t6, t7});
  Op o10 = tm.mkOp(Kind::GEQ);
  Term t11 = tm.mkTerm(o10, {t1, t3, t1});
  Sort s12 = t11.getSort();
  Term t13 = tm.mkTerm(Kind::BAG_COUNT, {t8, t9});
  Sort s14 = t13.getSort();
  Op o15 = tm.mkOp(Kind::BAG_CARD);
  Term t16 = tm.mkTerm(o15, {t6});
  Term t17 = tm.mkTerm(Kind::DISTINCT, {t16, t13});
  Term t18 = t11.andTerm(t17);
  Op o19 = tm.mkOp(Kind::VARIABLE_LIST);
  Term t20 = tm.mkTerm(o19, {t3, t2});
  Sort s21 = t20.getSort();
  Op o22 = tm.mkOp(Kind::EXISTS);
  Term t23 = tm.mkTerm(o22, {t20, t18});
  solver.assertFormula(t23);
  solver.checkSat();

  return 0;
}
