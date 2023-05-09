/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #600
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
Solver solver;
solver.setOption("incremental", "false");
solver.setOption("sets-ext", "true");
solver.setOption("check-abducts", "true");
solver.setOption("produce-abducts", "true");
Sort s0 = solver.mkUninterpretedSort("_u0");
Sort s1 = solver.getRoundingModeSort();
Sort s2 = solver.mkSetSort(s1);
Term t3 = solver.mkVar(s2, "_x1");
Term t4 = solver.mkConst(s2, "_x2");
Term t5 = solver.mkVar(s0, "_x4");
Term t6 = solver.mkVar(s1, "_x5");
Term t7 = solver.mkTerm(SET_IS_SINGLETON, {t4});
Sort s8 = t7.getSort();
Term t9 = solver.mkTerm(VARIABLE_LIST, {t6, t5, t3});
Sort s10 = t9.getSort();
Term t11 = solver.mkTerm(SET_COMPREHENSION, {t9, t7, t7});
Sort s12 = t11.getSort();
Term t13 = solver.mkTerm(SET_CHOOSE, {t11});
solver.assertFormula(t13);
Term t14 = solver.getAbduct(t13);

return 0;
}
