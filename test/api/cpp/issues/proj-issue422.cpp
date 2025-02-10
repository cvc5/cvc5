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
 * Test for project issue #422.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("strings-exp", "true");
  solver.setOption("sygus-abort-size", "1");
  Sort s1 = tm.mkBitVectorSort(36);
  Sort s2 = tm.getStringSort();
  Term t1 = tm.mkConst(s2, "_x0");
  Term t2 = tm.mkConst(s1, "_x1");
  Term t11;
  {
    uint32_t bw = s1.getBitVectorSize();
    std::string val(bw, '1');
    val[0] = '0';
    t11 = tm.mkBitVector(bw, val, 2);
  }
  Term t60 = tm.mkTerm(Kind::SET_SINGLETON, {t1});
  Term t66 = tm.mkTerm(Kind::BITVECTOR_COMP, {t2, t11});
  Term t92 = tm.mkRegexpAll();
  Term t96 = tm.mkTerm(tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {51}), {t66});
  Term t105 = tm.mkTerm(Kind::BITVECTOR_ADD, {t96, t96});
  Term t113 = tm.mkTerm(Kind::BITVECTOR_SUB, {t105, t105});
  Term t137 = tm.mkTerm(Kind::BITVECTOR_XOR, {t113, t105});
  Term t211 = tm.mkTerm(Kind::BITVECTOR_SLTBV, {t137, t137});
  Term t212 = tm.mkTerm(Kind::SET_MINUS, {t60, t60});
  Term t234 = tm.mkTerm(Kind::SET_CHOOSE, {t212});
  Term t250 = tm.mkTerm(Kind::STRING_REPLACE_RE_ALL, {t1, t92, t1});
  Term t259 = tm.mkTerm(Kind::STRING_REPLACE_ALL, {t234, t234, t250});
  Term t263 = tm.mkTerm(Kind::STRING_TO_LOWER, {t259});
  Term t272 = tm.mkTerm(Kind::BITVECTOR_SDIV, {t211, t66});
  Term t276 = tm.mkTerm(tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {71}), {t272});
  Term t288 = tm.mkTerm(Kind::EQUAL, {t263, t1});
  Term t300 = tm.mkTerm(Kind::BITVECTOR_SLT, {t276, t276});
  Term t301 = tm.mkTerm(Kind::EQUAL, {t288, t300});
  solver.assertFormula({t301});
  Term t = solver.findSynth(modes::FindSynthTarget::REWRITE_INPUT);
}
