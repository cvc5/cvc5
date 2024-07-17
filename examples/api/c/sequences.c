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
 * A simple demonstration of reasoning about sequences via the C API.
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

  // Sequence sort
  Cvc5Sort int_seq = cvc5_mk_sequence_sort(tm, cvc5_get_integer_sort(tm));

  // Sequence variables
  Cvc5Term x = cvc5_mk_const(tm, int_seq, "x");
  Cvc5Term y = cvc5_mk_const(tm, int_seq, "y");

  // Empty sequence
  Cvc5Term empty = cvc5_mk_empty_sequence(tm, cvc5_get_integer_sort(tm));
  // Sequence concatenation: x.y.empty
  Cvc5Term args3[3] = {x, y, empty};
  Cvc5Term concat = cvc5_mk_term(tm, CVC5_KIND_SEQ_CONCAT, 3, args3);
  // Sequence length: |x.y.empty|
  Cvc5Term args1[1] = {concat};
  Cvc5Term concat_len = cvc5_mk_term(tm, CVC5_KIND_SEQ_LENGTH, 1, args1);
  // |x.y.empty| > 1
  Cvc5Term args2[2] = {concat_len, cvc5_mk_integer_int64(tm, 1)};
  Cvc5Term formula1 = cvc5_mk_term(tm, CVC5_KIND_GT, 2, args2);
  // Sequence unit: seq(1)
  args1[0] = cvc5_mk_integer_int64(tm, 1);
  Cvc5Term unit = cvc5_mk_term(tm, CVC5_KIND_SEQ_UNIT, 1, args1);
  // x = seq(1)
  args2[0] = x;
  args2[1] = unit;
  Cvc5Term formula2 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // Make a query
  args2[0] = formula1;
  args2[1] = formula2;
  Cvc5Term q = cvc5_mk_term(tm, CVC5_KIND_AND, 2, args2);

  // check sat
  Cvc5Term assumptions[1] = {q};
  Cvc5Result result = cvc5_check_sat_assuming(slv, 1, assumptions);
  printf("cvc5 reports: %s is %s.\n",
         cvc5_term_to_string(q),
         cvc5_result_to_string(result));

  if (cvc5_result_is_sat(result))
  {
    printf("  x = %s\n", cvc5_term_to_string(cvc5_get_value(slv, x)));
    printf("  y = %s\n", cvc5_term_to_string(cvc5_get_value(slv, y)));
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
