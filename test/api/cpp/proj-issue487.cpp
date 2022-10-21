/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #487
 *
 */

#include "api/cpp/cvc5.h"
#include <cassert>

using namespace cvc5;

int main(void)
{
  Solver slv;
  Sort s1 = slv.getStringSort();
  Sort s2 = slv.mkSetSort(s1);
  Sort s3 = slv.mkBitVectorSort(73);
  Term t1 = slv.mkConst(s3, "_x0");
  Term t2 = slv.mkConst(s1, "_x1");
  Term t3 = slv.mkConst(s1, "_x2");
  Term t4;
  {
    uint32_t bw = s3.getBitVectorSize();
    std::string val(bw, '1');
    val[0] = '0';
    t4 = slv.mkBitVector(bw, val, 2);
  }
  Term t6 = slv.mkVar(s2, "_f3_0");
  Term t7 = slv.mkVar(s2, "_f3_1");
  Term t8 = slv.mkTerm(Kind::SET_INSERT, {t2, t6});
  Term t13 = slv.mkTerm(Kind::SET_SINGLETON, {t1});
  Term t18 = slv.mkTerm(Kind::SET_SINGLETON, {t3});
  Term t23 = slv.defineFun("_f3", {t6, t7}, t8.getSort(), t8);
  Term t26 = slv.mkTerm(Kind::SET_INSERT, {t4, t13});
  Term t27 = slv.mkTerm(Kind::BITVECTOR_UGE, {t1, t4});
  Term t31 = slv.mkTerm(Kind::SET_SINGLETON, {t4});
  Term t35 = slv.mkTerm(Kind::SET_CHOOSE, {t26});
  Term t38 = slv.mkTerm(Kind::SET_INTER, {t31, t26});
  Term t39 = slv.mkTerm(Kind::ITE, {t27, t38, t31});
  Term t40 = slv.mkTerm(Kind::SET_CHOOSE, {t39});
  Term t51 = slv.mkTerm(Kind::SET_INSERT, {t40, t35, t13});
  Term t75 = slv.mkTerm(Kind::APPLY_UF, {t23, t18, t18});
  Term t98 = slv.mkTerm(Kind::SET_CARD, {t75});
  Term t101 = slv.mkTerm(Kind::DIVISION, {t98, t98});
  Term t98r = slv.mkTerm(Kind::TO_REAL, {t98});
  Term t139 = slv.mkTerm(Kind::EQUAL, {t101, t98r});
  Term t142 = slv.mkTerm(Kind::SET_SUBSET, {t13, t51});
  Term t217 = slv.mkTerm(Kind::IMPLIES, {t142, t139});
  slv.checkSatAssuming({t217});
}
