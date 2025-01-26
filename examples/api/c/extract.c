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
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector solver.
 *
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_logic(slv, "QF_BV");

  Cvc5Sort bv32 = cvc5_mk_bv_sort(tm, 32);

  Cvc5Term x = cvc5_mk_const(tm, bv32, "x");

  uint32_t idxs[2] = {31, 1};
  Cvc5Op ext_31_1 = cvc5_mk_op(tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs);
  Cvc5Term args1[1] = {x};
  Cvc5Term x_31_1 = cvc5_mk_term_from_op(tm, ext_31_1, 1, args1);

  idxs[0] = 30;
  idxs[1] = 0;
  Cvc5Op ext_30_0 = cvc5_mk_op(tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs);
  Cvc5Term x_30_0 = cvc5_mk_term_from_op(tm, ext_30_0, 1, args1);

  idxs[0] = 31;
  idxs[1] = 31;
  Cvc5Op ext_31_31 = cvc5_mk_op(tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs);
  Cvc5Term x_31_31 = cvc5_mk_term_from_op(tm, ext_31_31, 1, args1);

  idxs[0] = 0;
  idxs[1] = 0;
  Cvc5Op ext_0_0 = cvc5_mk_op(tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs);
  Cvc5Term x_0_0 = cvc5_mk_term_from_op(tm, ext_0_0, 1, args1);

  Cvc5Term args2[2] = {x_31_1, x_30_0};
  Cvc5Term eq = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  printf(" Asserting: %s\n", cvc5_term_to_string(eq));
  cvc5_assert_formula(slv, eq);

  args2[0] = x_31_31;
  args2[1] = x_0_0;
  Cvc5Term dis = cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2);
  printf(" Check sat assuming: %s\n", cvc5_term_to_string(dis));
  printf(" Expect UNSAT.\n");
  Cvc5Term assumptions[1] = {dis};
  printf(" cvc5: %s\n",
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
