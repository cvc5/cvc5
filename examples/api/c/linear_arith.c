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
 * A simple demonstration of the linear arithmetic solving capabilities and
 * the push pop of cvc5. This also gives an example option.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_logic(slv, "QF_LIRA");

  // Prove that if given x (Integer) and y (Real) then
  // the maximum value of y - x is 2/3

  // Sorts
  Cvc5Sort real = cvc5_get_real_sort(tm);
  Cvc5Sort integer = cvc5_get_integer_sort(tm);

  // Variables
  Cvc5Term x = cvc5_mk_const(tm, integer, "x");
  Cvc5Term y = cvc5_mk_const(tm, real, "y");

  // Constants
  Cvc5Term three = cvc5_mk_integer_int64(tm, 3);
  Cvc5Term neg2 = cvc5_mk_integer_int64(tm, -2);
  Cvc5Term two_thirds = cvc5_mk_real_num_den(tm, 2, 3);

  // Terms
  Cvc5Term args2[2] = {three, y};
  Cvc5Term three_y = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, args2);
  args2[0] = y;
  args2[1] = x;
  Cvc5Term diff = cvc5_mk_term(tm, CVC5_KIND_SUB, 2, args2);

  // Formulas
  args2[0] = x;
  args2[1] = three_y;
  Cvc5Term x_geq_3y = cvc5_mk_term(tm, CVC5_KIND_GEQ, 2, args2);
  args2[0] = x;
  args2[1] = y;
  Cvc5Term x_leq_y = cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2);
  args2[0] = neg2;
  args2[1] = x;
  Cvc5Term neg2_lt_x = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);

  Cvc5Term args3[3] = {x_geq_3y, x_leq_y, neg2_lt_x};
  Cvc5Term assertions = cvc5_mk_term(tm, CVC5_KIND_AND, 3, args3);

  printf("Given the assertions %s\n", cvc5_term_to_string(assertions));
  cvc5_assert_formula(slv, assertions);

  cvc5_push(slv, 1);
  args2[0] = diff;
  args2[1] = two_thirds;
  Cvc5Term diff_leq_two_thirds = cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2);
  printf("Prove that %s with cvc5.\n",
         cvc5_term_to_string(diff_leq_two_thirds));
  printf("cvc5 should report UNSAT.\n");
  Cvc5Term args1[1] = {diff_leq_two_thirds};
  Cvc5Term assumptions[1] = {cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1)};
  printf("Result from cvc5 is: %s\n\n",
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
  cvc5_pop(slv, 1);

  cvc5_push(slv, 1);
  args2[0] = diff;
  args2[1] = two_thirds;
  Cvc5Term diff_is_two_thirds = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  cvc5_assert_formula(slv, diff_is_two_thirds);
  printf("Show that the assertions are consistent with \n");
  printf("%s with cvc5.\n", cvc5_term_to_string(diff_is_two_thirds));
  printf("cvc5 should report SAT.\n");
  printf("Result from cvc5 is: %s\n",
         cvc5_result_to_string(cvc5_check_sat(slv)));
  cvc5_pop(slv, 1);

  printf("Thus the maximum value of (y - x) is 2/3.\n");

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
