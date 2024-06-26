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
 * A simple demonstration of the transcendental extension.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_logic(slv, "QF_NRAT");

  Cvc5Sort real_sort = cvc5_get_real_sort(tm);

  // Variables
  Cvc5Term x = cvc5_mk_const(tm, real_sort, "x");
  Cvc5Term y = cvc5_mk_const(tm, real_sort, "y");

  // Helper terms
  Cvc5Term two = cvc5_mk_real_int64(tm, 2);
  Cvc5Term pi = cvc5_mk_pi(tm);
  Cvc5Term args2[2] = {two, pi};
  Cvc5Term twopi = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, args2);
  args2[0] = y;
  args2[1] = y;
  Cvc5Term ysq = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, args2);
  Cvc5Term args1[1] = {x};
  Cvc5Term sinx = cvc5_mk_term(tm, CVC5_KIND_SINE, 1, args1);

  // Formulas
  args2[0] = x;
  args2[1] = pi;
  Cvc5Term x_gt_pi = cvc5_mk_term(tm, CVC5_KIND_GT, 2, args2);
  args2[0] = x;
  args2[1] = twopi;
  Cvc5Term x_lt_pi = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);
  args2[0] = ysq;
  args2[1] = sinx;
  Cvc5Term ysq_lt_sinx = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);

  cvc5_assert_formula(slv, x_gt_pi);
  cvc5_assert_formula(slv, x_lt_pi);
  cvc5_assert_formula(slv, ysq_lt_sinx);

  printf("cvc5 should report UNSAT.\n");
  printf("Result from cvc5 is: %s\n",
         cvc5_result_to_string(cvc5_check_sat(slv)));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
