/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #487
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  Sort s1 = tm.getStringSort();
  Sort s2 = tm.mkSetSort(s1);
  Sort s3 = tm.mkBitVectorSort(73);
  Term t1 = tm.mkConst(s3, "_x0");
  Term t2 = tm.mkConst(s1, "_x1");
  Term t3 = tm.mkConst(s1, "_x2");
  Term t4;
  {
    uint32_t bw = s3.getBitVectorSize();
    std::string val(bw, '1');
    val[0] = '0';
    t4 = tm.mkBitVector(bw, val, 2);
  }
  Term t6 = tm.mkVar(s2, "_f3_0");
  Term t7 = tm.mkVar(s2, "_f3_1");
  Term t8 = tm.mkTerm(Kind::SET_INSERT, {t2, t6});
  Term t13 = tm.mkTerm(Kind::SET_SINGLETON, {t1});
  Term t18 = tm.mkTerm(Kind::SET_SINGLETON, {t3});
  Term t23 = solver.defineFun("_f3", {t6, t7}, t8.getSort(), t8);
  Term t26 = tm.mkTerm(Kind::SET_INSERT, {t4, t13});
  Term t27 = tm.mkTerm(Kind::BITVECTOR_UGE, {t1, t4});
  Term t31 = tm.mkTerm(Kind::SET_SINGLETON, {t4});
  Term t35 = tm.mkTerm(Kind::SET_CHOOSE, {t26});
  Term t38 = tm.mkTerm(Kind::SET_INTER, {t31, t26});
  Term t39 = tm.mkTerm(Kind::ITE, {t27, t38, t31});
  Term t40 = tm.mkTerm(Kind::SET_CHOOSE, {t39});
  Term t51 = tm.mkTerm(Kind::SET_INSERT, {t40, t35, t13});
  Term t75 = tm.mkTerm(Kind::APPLY_UF, {t23, t18, t18});
  Term t98 = tm.mkTerm(Kind::SET_CARD, {t75});
  Term t101 = tm.mkTerm(Kind::DIVISION, {t98, t98});
  Term t139 = tm.mkTerm(Kind::EQUAL, {t101, tm.mkTerm(Kind::TO_REAL, {t98})});
  Term t142 = tm.mkTerm(Kind::SET_SUBSET, {t13, t51});
  Term t217 = tm.mkTerm(Kind::IMPLIES, {t142, t139});
  solver.checkSatAssuming({t217});

  return 0;
}
