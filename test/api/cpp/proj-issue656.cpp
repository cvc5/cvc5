/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #656
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-abducts", "true");
  Sort s0 = solver.getIntegerSort();
  Sort s1 = solver.mkUninterpretedSort("_u0");
  Term t2 = solver.mkConst(s1, "_x7");
  Term t3 = solver.mkInteger(28601551);
  Term t4 = solver.mkTerm(Kind::SEQ_UNIT, {t2});
  Sort s5 = t4.getSort();
  Term t6 = solver.mkTerm(Kind::BAG_MAKE, {t2, t3});
  Sort s7 = t6.getSort();
  Term t8 = solver.mkTerm(Kind::BAG_UNION_DISJOINT, {t6, t6});
  Op o9 = solver.mkOp(Kind::BAG_CARD);
  Term t10 = solver.mkTerm(o9, {t8});
  Op o11 = solver.mkOp(Kind::SEQ_UPDATE);
  Term t12 = solver.mkTerm(o11, {t4, t10, t4});
  Op o13 = solver.mkOp(Kind::SEQ_CONTAINS);
  Term t14 = solver.mkTerm(o13, {t4, t12});
  Sort s15 = t14.getSort();
  Term t16 = solver.getAbduct(t14);

  return 0;
}