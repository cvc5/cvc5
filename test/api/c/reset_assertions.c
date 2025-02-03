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
 * A simple test for cvc5_reset_assertions().
 *
 * This indirectly also tests some corner cases w.r.t. context-dependent
 * datastructures: resetAssertions() pops the contexts to zero but some
 * context-dependent datastructures are created at leevel 1, which the
 * datastructure needs to handle properly problematic.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* solver = cvc5_new(tm);
  cvc5_set_option(solver, "incremental", "true");

  Cvc5Term x = cvc5_mk_const(tm, cvc5_get_real_sort(tm), "x");
  Cvc5Term four = cvc5_mk_real_int64(tm, 4);
  Cvc5Term args[2] = {x, four};
  Cvc5Term x_eq_four = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);
  cvc5_assert_formula(solver, x_eq_four);
  printf("%s\n", cvc5_result_to_string(cvc5_check_sat(solver)));

  cvc5_reset_assertions(solver);

  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  Cvc5Sort arr_sort = cvc5_mk_array_sort(tm, int_sort, int_sort);
  Cvc5Term array = cvc5_mk_const(tm, arr_sort, "array");
  Cvc5Term four_int = cvc5_mk_integer_int64(tm, 4);
  args[0] = array;
  args[1] = four_int;
  Cvc5Term arr_at_four = cvc5_mk_term(tm, CVC5_KIND_SELECT, 2, args);
  Cvc5Term ten = cvc5_mk_integer_int64(tm, 10);
  args[0] = arr_at_four;
  args[1] = ten;
  Cvc5Term arr_at_four_eq_ten = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);
  cvc5_assert_formula(solver, arr_at_four_eq_ten);
  printf("%s\n", cvc5_result_to_string(cvc5_check_sat(solver)));
  cvc5_delete(solver);
  cvc5_term_manager_delete(tm);
}
