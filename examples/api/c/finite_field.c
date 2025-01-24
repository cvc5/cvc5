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
 * An example of solving finite field problems with cvc5's cpp API.
 */

#include <assert.h>
#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");

  Cvc5Sort f5 = cvc5_mk_ff_sort(tm, "5", 10);
  Cvc5Term a = cvc5_mk_const(tm, f5, "a");
  Cvc5Term b = cvc5_mk_const(tm, f5, "b");
  Cvc5Term z = cvc5_mk_ff_elem(tm, "0", f5, 10);

  Cvc5Term args2[2] = {a, b};
  Cvc5Term ff_mul = cvc5_mk_term(tm, CVC5_KIND_FINITE_FIELD_MULT, 2, args2);
  args2[0] = ff_mul;
  args2[1] = cvc5_mk_ff_elem(tm, "-1", f5, 10);
  Cvc5Term ff_add = cvc5_mk_term(tm, CVC5_KIND_FINITE_FIELD_ADD, 2, args2);
  args2[0] = ff_add;
  args2[1] = z;
  Cvc5Term inv = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  args2[0] = a;
  args2[1] = cvc5_mk_ff_elem(tm, "-2", f5, 10);
  cvc5_term_release(ff_add);  // optional, not needed anymore so we can release
  ff_add = cvc5_mk_term(tm, CVC5_KIND_FINITE_FIELD_ADD, 2, args2);
  args2[0] = ff_add;
  args2[1] = z;
  Cvc5Term a_is_two = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // ab - 1 = 0
  cvc5_assert_formula(slv, inv);
  // a = 2
  cvc5_assert_formula(slv, a_is_two);

  // should be SAT, with b = 2^(-1)
  Cvc5Result r = cvc5_check_sat(slv);
  assert(cvc5_result_is_sat(r));

  printf("a = %s\n", cvc5_term_to_string(cvc5_get_value(slv, a)));
  printf("b = %s\n", cvc5_term_to_string(cvc5_get_value(slv, b)));

  // b = 2
  args2[0] = b;
  args2[1] = cvc5_mk_ff_elem(tm, "-2", f5, 10);
  cvc5_term_release(ff_add);  // optional, not needed anymore so we can release
  ff_add = cvc5_mk_term(tm, CVC5_KIND_FINITE_FIELD_ADD, 2, args2);
  args2[0] = ff_add;
  args2[1] = z;
  Cvc5Term b_is_two = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // should be UNSAT, 2*2 - 1 != 0
  cvc5_assert_formula(slv, b_is_two);

  cvc5_result_release(r);  // optional, not needed anymore so we can release
  r = cvc5_check_sat(slv);
  assert(cvc5_result_is_unsat(r));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
