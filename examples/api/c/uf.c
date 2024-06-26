/******************************************************************************
 * Top contributors (to current version):
 *  Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the capabilities of the cvc5 uf solver.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_logic(slv, "QF_UF");

  // Sorts
  Cvc5Sort un_sort = cvc5_mk_uninterpreted_sort(tm, "U");
  Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);
  Cvc5Sort domain[1] = {un_sort};
  Cvc5Sort un_to_un_sort = cvc5_mk_fun_sort(tm, 1, domain, un_sort);
  Cvc5Sort un_pred_sort = cvc5_mk_fun_sort(tm, 1, domain, bool_sort);

  // Variables
  Cvc5Term x = cvc5_mk_const(tm, un_sort, "x");
  Cvc5Term y = cvc5_mk_const(tm, un_sort, "y");

  // Functions
  Cvc5Term f = cvc5_mk_const(tm, un_to_un_sort, "f");
  Cvc5Term p = cvc5_mk_const(tm, un_pred_sort, "p");

  // Terms
  Cvc5Term args2[2] = {f, x};
  Cvc5Term f_x = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args2);
  args2[1] = y;
  Cvc5Term f_y = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args2);
  args2[0] = p;
  args2[1] = f_x;
  Cvc5Term p_f_x = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args2);
  args2[1] = f_y;
  Cvc5Term p_f_y = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args2);

  // Construct the assertions
  Cvc5Term not_p_f_x = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, &p_f_x);
  args2[0] = x;
  args2[1] = f_x;
  Cvc5Term eq1 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = y;
  args2[1] = f_y;
  Cvc5Term eq2 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = eq1;
  args2[1] = eq2;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_AND, 2, args2));
  cvc5_assert_formula(slv, not_p_f_x);
  cvc5_assert_formula(slv, p_f_y);

  printf("%s\n", cvc5_result_to_string(cvc5_check_sat(slv)));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
