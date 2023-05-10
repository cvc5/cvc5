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
 * Test for project issue #538
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
Solver solver;
solver.setOption("incremental", "false");
Sort s0 = solver.mkBitVectorSort(128);
Term t1 = solver.mkConst(s0, "_x2");
Op o2 = solver.mkOp(BITVECTOR_TO_NAT);
Term t3 = solver.mkTerm(o2, {t1});
Sort s4 = t3.getSort();
Op o5 = solver.mkOp(INT_TO_BITVECTOR, {27});
Term t6 = solver.mkTerm(o5, {t3});
Sort s7 = t6.getSort();
Op o8 = solver.mkOp(BITVECTOR_SGE);
Term t9 = solver.mkTerm(o8, {t6, t6});
Sort s10 = t9.getSort();
solver.checkSatAssuming({t9, t9});

return 0;
}
