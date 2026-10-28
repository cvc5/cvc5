/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #663
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
  solver.setOption("check-unsat-cores", "true");
  solver.setOption("sets-exp", "true");
  solver.setOption("strings-exp", "true");
  solver.setOption("fp-exp", "true");
  solver.setOption("fmf-bound", "true");
  solver.setOption("arith-rewrite-equalities", "false");
  solver.setOption("produce-unsat-assumptions", "true");
  solver.setOption("sygus-rr-synth-filter-order", "true");
  solver.setOption("incremental", "true");
  solver.setOption("debug-check-models", "true");
  solver.setOption("produce-models", "true");
  solver.setOption("dio-turns", "162793396514338764");
  solver.setOption("produce-unsat-cores", "true");
  solver.setOption("multi-trigger-when-single", "true");
  solver.setOption("error-selection-rule", "max");
  solver.setOption("minisat-simplification", "clause-elim");
  solver.setOption("enum-inst-stratify", "true");
  solver.setOption("enum-inst-interleave", "false");
  Sort s0 = tm.getRoundingModeSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = tm.mkVar(s0, "_x1");
  Term t3 = tm.mkConst(s0, "_x2");
  Term t4 = tm.mkConst(s0, "_x3");
  Term t5 = tm.mkConst(s0, "_x4");
  Sort s6 = tm.mkBagSort(s0);
  Sort s7 = tm.getRealSort();
  Sort s8 = tm.mkFunctionSort({s6}, s7);
  Sort s9 = tm.getRoundingModeSort();
  Sort s10 = tm.mkArraySort(s7, s7);
  Term t11 = tm.mkConst(s0, "_x5");
  Term t12 = tm.mkReal(75, 88);
  Term t13 = tm.mkVar(s7, "_x10");
  Term t14 = tm.mkVar(s0, "_x11");
  Term t15 = tm.mkConst(s10, "_x12");
  Term t16 = tm.mkVar(s0, "_x13");
  Term t17 = tm.mkConst(s7, "_x14");
  Term t18 = tm.mkReal("1998772261844469067102002405584");
  Term t19 = tm.mkReal("87419418096854089889513573545296029053187");
  Term t20 = tm.mkConst(s6, "_x15");
  Term t21 = tm.mkReal("23607830097.565774338676119586533424");
  Term t22 = tm.mkVar(s7, "_x16");
  Term t23 = tm.mkConst(s8, "_x17");
  Term t24 = tm.mkConst(s8, "_x18");
  Term t25 = tm.mkReal("85464727.20438923257");
  Term t26 = tm.mkConst(s10, "_x19");
  Term t27 = tm.mkVar(s10, "_x20");
  Term t28 = tm.mkReal("2649363/89394287");
  Term t29 = tm.mkVar(s7, "_x21");
  Op o30 = tm.mkOp(Kind::BAG_INTER_MIN);
  Term t31 = tm.mkTerm(o30, {t20, t20});
  Term t32 = tm.mkTerm(Kind::SEQ_UNIT, {t28});
  Sort s33 = t32.getSort();
  Op o34 = tm.mkOp(Kind::SEQ_PREFIX);
  Term t35 = tm.mkTerm(o34, {t32, t32});
  Sort s36 = t35.getSort();
  solver.checkSatAssuming({t35, t35, t35});
  solver.blockModelValues({t20});
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::VALUES);
  solver.checkSat();

  return 0;
}
