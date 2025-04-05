/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #434.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("dump-difficulty", "true");
  solver.setOption("debug-check-models", "true");
  Sort s1 = tm.mkUninterpretedSort("_u0");
  Sort s4 = tm.getBooleanSort();
  Term t1 = tm.mkConst(s1, "_x3");
  Term t15 = tm.mkConst(s1, "_x17");
  Term t26 = tm.mkBoolean(false);
  Term t60 = tm.mkVar(s4, "_f29_1");
  Term t73 = solver.defineFun("_f29", {t60}, t60.getSort(), t60);
  Term t123 = tm.mkVar(s4, "_f31_0");
  Term t135 = solver.defineFun("_f31", {t123}, t123.getSort(), t123);
  Term t507 = tm.mkVar(s4, "_f37_1");
  Term t510 = tm.mkTerm(Kind::APPLY_UF, {t73, t507});
  Term t530 = solver.defineFun("_f37", {t507}, t510.getSort(), t510);
  Term t559 = tm.mkTerm(Kind::DISTINCT, {t15, t1});
  Term t631 = tm.mkTerm(Kind::XOR, {t559, t26});
  Term t632 = tm.mkTerm(Kind::APPLY_UF, {t135, t631});
  Term t715 = tm.mkVar(s4, "_f40_0");
  Term t721 = tm.mkTerm(Kind::APPLY_UF, {t530, t715});
  Term t722 = tm.mkTerm(Kind::APPLY_UF, {t530, t721});
  Term t731 = solver.defineFun("_f40", {t715}, t722.getSort(), t722);
  Term t1014 = tm.mkVar(s4, "_f45_0");
  Term t1034 = tm.mkTerm(Kind::DISTINCT, {t510, t510});
  Term t1035 = tm.mkTerm(Kind::XOR, {t1034, t632});
  Term t1037 = tm.mkTerm(Kind::APPLY_UF, {t135, t1035});
  Term t1039 = tm.mkTerm(Kind::APPLY_UF, {t731, t1037});
  Term t1040 = solver.defineFun("_f45", {t1014}, t1039.getSort(), t1039);
  Term t1072 = tm.mkTerm(Kind::APPLY_UF, {t1040, t510});
  Term t1073 = tm.mkTerm(Kind::APPLY_UF, {t73, t1072});
  // the query has free variables, and should throw an exception
  try
  {
    solver.checkSatAssuming({t1073, t510});
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
