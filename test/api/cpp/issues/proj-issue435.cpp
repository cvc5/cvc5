/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #435.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("strings-exp", "true");
  Sort s1 = tm.mkUninterpretedSort("_u0");
  Sort s3 = tm.getBooleanSort();
  Sort _p7 = tm.mkParamSort("_p7");
  DatatypeDecl _dt5 = tm.mkDatatypeDecl("_dt5", {_p7});
  DatatypeConstructorDecl _cons33 = tm.mkDatatypeConstructorDecl("_cons33");
  _cons33.addSelector("_sel31", s1);
  _cons33.addSelector("_sel32", _p7);
  _dt5.addConstructor(_cons33);
  std::vector<Sort> _s6 = tm.mkDatatypeSorts({_dt5});
  Sort s6 = _s6[0];
  Sort s21 = s6.instantiate({s3});
  Sort s42 = tm.mkSequenceSort(s21);
  Term t40 = tm.mkConst(s42, "_x64");
  Term t75 = tm.mkTerm(Kind::SEQ_REV, {t40});
  Term t91 = tm.mkTerm(Kind::SEQ_PREFIX, {t75, t40});
  solver.checkSatAssuming({t91});
}
