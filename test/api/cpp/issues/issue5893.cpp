/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #5893.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Sort bvsort4 = tm.mkBitVectorSort(4);
  Sort bvsort8 = tm.mkBitVectorSort(8);
  Sort arrsort = tm.mkArraySort(bvsort4, bvsort8);
  Term arr = tm.mkConst(arrsort, "arr");
  Term idx = tm.mkConst(bvsort4, "idx");
  Term ten = tm.mkBitVector(8, "10", 10);
  Term sel = tm.mkTerm(Kind::SELECT, {arr, idx});
  Term distinct = tm.mkTerm(Kind::DISTINCT, {sel, ten});
  (void)distinct.getOp();
}
