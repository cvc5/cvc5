/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #436.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("produce-abducts", "true");
  solver.setOption("solve-bv-as-int", "sum");
  Sort s8 = tm.mkBitVectorSort(68);
  Term t17 = tm.mkConst(s8, "_x6");
  Term t23;
  {
    uint32_t bw = s8.getBitVectorSize();
    t23 = tm.mkBitVector(bw, 1);
  }
  Term t33 = tm.mkTerm(Kind::BITVECTOR_ULT, {t17, t23});
  // solve-bv-as-int is incompatible with get-abduct
  try
  {
    solver.getAbduct(t33);
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
