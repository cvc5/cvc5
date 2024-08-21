/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #420.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("strings-exp", "true");
  solver.setOption("produce-models", "true");
  solver.setOption("produce-unsat-cores", "true");
  Sort s2 = tm.getRealSort();
  Sort s3 = tm.mkUninterpretedSort("_u0");
  DatatypeDecl _dt1 = tm.mkDatatypeDecl("_dt1", {});
  DatatypeConstructorDecl _cons16 = tm.mkDatatypeConstructorDecl("_cons16");
  _cons16.addSelector("_sel13", s3);
  _dt1.addConstructor(_cons16);
  std::vector<Sort> _s4 = tm.mkDatatypeSorts({_dt1});
  Sort s4 = _s4[0];
  Sort s5 = tm.mkSequenceSort(s2);
  Term t3 = tm.mkConst(s5, "_x18");
  Term t7 = tm.mkConst(s4, "_x22");
  // was initially a dt size application
  Term t13 = tm.mkConst(tm.getIntegerSort(), "t13");
  Term t53 = tm.mkTerm(Kind::SEQ_NTH, {t3, t13});
  solver.checkSat();
  solver.blockModelValues({t53, t7});
  solver.checkSat();
}
