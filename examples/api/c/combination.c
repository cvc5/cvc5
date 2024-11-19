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
 * A simple demonstration of the capabilities of cvc5
 *
 * A simple demonstration of how to use uninterpreted functions, combining this
 * with arithmetic, and extracting a model at the end of a satisfiable query.
 * The model is displayed using getValue().
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

void prefix_print_get_value(Cvc5* slv, Cvc5Term t, int32_t level)
{
  // Note: The const char* returned by cvc5_term_to_string is only valid
  //       until the next call to cvc5_term_to_string. Thus, we cannot
  //       chain calls to this function in a single printf statement.
  printf("slv.getValue(%s): ", cvc5_term_to_string(t));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, t)));

  for (size_t i = 0, n = cvc5_term_get_num_children(t); i < n; ++i)
  {
    prefix_print_get_value(slv, cvc5_term_get_child(t, i), level + 1);
  }
}

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_set_option(slv, "dag-thresh", "0");
  cvc5_set_logic(slv, "QF_UFLIRA");

  // Sorts
  Cvc5Sort un_sort = cvc5_mk_uninterpreted_sort(tm, "u");
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);
  Cvc5Sort domain[1] = {un_sort};
  Cvc5Sort un_to_int_sort = cvc5_mk_fun_sort(tm, 1, domain, int_sort);
  domain[0] = int_sort;
  Cvc5Sort int_pred_sort = cvc5_mk_fun_sort(tm, 1, domain, bool_sort);

  // Variables
  Cvc5Term x = cvc5_mk_const(tm, un_sort, "x");
  Cvc5Term y = cvc5_mk_const(tm, un_sort, "y");

  // Functions
  Cvc5Term f = cvc5_mk_const(tm, un_to_int_sort, "f");
  Cvc5Term p = cvc5_mk_const(tm, int_pred_sort, "p");

  // Constants
  Cvc5Term zero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(tm, 1);

  // Terms
  Cvc5Term args[2] = {f, x};
  Cvc5Term f_x = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args);
  args[1] = y;
  Cvc5Term f_y = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args);
  args[0] = f_x;
  args[1] = f_y;
  Cvc5Term sum = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args);
  args[0] = p;
  args[1] = zero;
  Cvc5Term p_0 = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args);
  args[0] = p;
  args[1] = f_y;
  Cvc5Term p_f_y = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, args);

  // Construct the assertions
  Cvc5Term args0[2] = {zero, f_x};
  Cvc5Term args1[2] = {zero, f_y};
  Cvc5Term args2[2] = {sum, one};
  Cvc5Term args3[1] = {p_0};

  Cvc5Term aargs[5] = {
      cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args0),  // 0 <= f(x)
      cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args1),  // 0 <= f(y)
      cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2),  // f(x) + f(y) <= 1
      cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args3),  // not p(0)
      p_f_y};
  Cvc5Term assertions = cvc5_mk_term(tm, CVC5_KIND_AND, 5, aargs);
  cvc5_assert_formula(slv, assertions);

  printf("Given the following assertions:\n");
  printf("%s\n\n", cvc5_term_to_string(assertions));

  printf("Prove x /= y is entailed.\n");
  args[0] = x;
  args[1] = y;
  Cvc5Term assumptions[1] = {cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args)};
  printf("cvc5: %s.\n\n",
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));

  printf("Call checkSat to show that the assertions are satisfiable.\n");
  printf("cvc5: %s.\n\n", cvc5_result_to_string(cvc5_check_sat(slv)));

  printf("Call slv.getValue(...) on terms of interest.\n");
  printf("cvc5_get_value(slv, %s): ", cvc5_term_to_string(f_x));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, f_x)));
  printf("cvc5_get_value(slv, %s): ", cvc5_term_to_string(f_y));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, f_y)));
  printf("cvc5_get_value(slv, %s): ", cvc5_term_to_string(sum));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, sum)));
  printf("cvc5_get_value(slv, %s): ", cvc5_term_to_string(p_0));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, p_0)));
  printf("cvc5_get_value(slv, %s): ", cvc5_term_to_string(p_f_y));
  printf("%s\n\n", cvc5_term_to_string(cvc5_get_value(slv, p_f_y)));

  printf(
      "Alternatively, iterate over assertions and call slv.getValue(...) on "
      "all terms.\n");
  prefix_print_get_value(slv, assertions, 0);
  printf("\n");

  printf("You can also use nested loops to iterate over terms.\n");
  for (size_t i = 0, n = cvc5_term_get_num_children(assertions); i < n; ++i)
  {
    Cvc5Term child = cvc5_term_get_child(assertions, i);
    printf("term: %s\n", cvc5_term_to_string(child));
    for (size_t j = 0, m = cvc5_term_get_num_children(child); j < m; ++j)
    {
      printf(" + child: %s\n",
             cvc5_term_to_string(cvc5_term_get_child(child, j)));
    }
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
