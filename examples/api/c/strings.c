/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tianyi Liang, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about strings via the C API.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  // Set the logic
  cvc5_set_logic(slv, "QF_SLIA");
  // Produce models
  cvc5_set_option(slv, "produce-models", "true");
  // The option strings-exp is needed
  cvc5_set_option(slv, "strings-exp", "true");

  // String type
  Cvc5Sort string_sort = cvc5_get_string_sort(tm);

  // String constants
  Cvc5Term ab = cvc5_mk_string(tm, "ab", false);
  Cvc5Term abc = cvc5_mk_string(tm, "abc", false);
  // String variables
  Cvc5Term x = cvc5_mk_const(tm, string_sort, "x");
  Cvc5Term y = cvc5_mk_const(tm, string_sort, "y");
  Cvc5Term z = cvc5_mk_const(tm, string_sort, "z");

  // String concatenation: x.ab.y
  Cvc5Term args3[3] = {x, ab, y};
  Cvc5Term lhs = cvc5_mk_term(tm, CVC5_KIND_STRING_CONCAT, 3, args3);
  // String concatenation: abc.z
  Cvc5Term args2[2] = {abc, z};
  Cvc5Term rhs = cvc5_mk_term(tm, CVC5_KIND_STRING_CONCAT, 2, args2);
  // x.ab.y = abc.z
  args2[0] = lhs;
  args2[1] = rhs;
  Cvc5Term formula1 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // Length of y: |y|
  Cvc5Term args1[1] = {y};
  Cvc5Term len_y = cvc5_mk_term(tm, CVC5_KIND_STRING_LENGTH, 1, args1);
  // |y| >= 0
  args2[0] = len_y;
  args2[1] = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term formula2 = cvc5_mk_term(tm, CVC5_KIND_GEQ, 2, args2);

  // Regular expression: (ab[c-e]*f)|g|h
  args2[0] = cvc5_mk_string(tm, "c", false);
  args2[1] = cvc5_mk_string(tm, "e", false);
  Cvc5Term range = cvc5_mk_term(tm, CVC5_KIND_REGEXP_RANGE, 2, args2);
  args1[0] = range;
  Cvc5Term reg_star = cvc5_mk_term(tm, CVC5_KIND_REGEXP_STAR, 1, args1);
  args1[0] = cvc5_mk_string(tm, "ab", false);
  args3[0] = cvc5_mk_term(tm, CVC5_KIND_STRING_TO_REGEXP, 1, args1);
  args3[1] = reg_star;
  args1[0] = cvc5_mk_string(tm, "f", false);
  args3[2] = cvc5_mk_term(tm, CVC5_KIND_STRING_TO_REGEXP, 1, args1);
  Cvc5Term concat = cvc5_mk_term(tm, CVC5_KIND_REGEXP_CONCAT, 3, args3);
  args3[0] = concat;
  args1[0] = cvc5_mk_string(tm, "g", false);
  args3[1] = cvc5_mk_term(tm, CVC5_KIND_STRING_TO_REGEXP, 1, args1);
  args1[0] = cvc5_mk_string(tm, "h", false);
  args3[2] = cvc5_mk_term(tm, CVC5_KIND_STRING_TO_REGEXP, 1, args1);
  Cvc5Term r = cvc5_mk_term(tm, CVC5_KIND_REGEXP_UNION, 3, args3);

  // String variables
  Cvc5Term s1 = cvc5_mk_const(tm, string_sort, "s1");
  Cvc5Term s2 = cvc5_mk_const(tm, string_sort, "s2");
  // String concatenation: s1.s2
  args2[0] = s1;
  args2[1] = s2;
  Cvc5Term s = cvc5_mk_term(tm, CVC5_KIND_STRING_CONCAT, 2, args2);

  // s1.s2 in (ab[c-e]*f)|g|h
  args2[0] = s;
  args2[1] = r;
  Cvc5Term formula3 = cvc5_mk_term(tm, CVC5_KIND_STRING_IN_REGEXP, 2, args2);

  // Make a query
  args3[0] = formula1;
  args3[1] = formula2;
  args3[2] = formula3;
  Cvc5Term q = cvc5_mk_term(tm, CVC5_KIND_AND, 3, args3);

  // check sat
  Cvc5Term assumptions[1] = {q};
  Cvc5Result result = cvc5_check_sat_assuming(slv, 1, assumptions);
  printf("cvc5 reports: %s is %s.\n",
         cvc5_term_to_string(q),
         cvc5_result_to_string(result));

  if (cvc5_result_is_sat(result))
  {
    printf("  x  = %s\n", cvc5_term_to_string(cvc5_get_value(slv, x)));
    printf("  s1.s2 = %s\n", cvc5_term_to_string(cvc5_get_value(slv, s)));
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
