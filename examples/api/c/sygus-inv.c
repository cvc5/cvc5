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
 * A simple demonstration of the Sygus API.
 *
 * A simple demonstration of how to use the Sygus API to synthesize a simple
 * invariant.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

#include "utils.h"

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  // required options
  cvc5_set_option(slv, "sygus", "true");
  cvc5_set_option(slv, "incremental", "false");

  // set the logic
  cvc5_set_logic(slv, "LIA");

  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);

  Cvc5Term zero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(tm, 1);
  Cvc5Term ten = cvc5_mk_integer_int64(tm, 10);

  // declare input variables for functions
  Cvc5Term x = cvc5_mk_var(tm, int_sort, "x");
  Cvc5Term xp = cvc5_mk_var(tm, int_sort, "xp");

  // (ite (< x 10) (= xp (+ x 1)) (= xp x))
  Cvc5Term args2[2] = {x, ten};
  Cvc5Term cond = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);
  args2[0] = x;
  args2[1] = one;
  Cvc5Term add = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);
  args2[0] = xp;
  args2[1] = add;
  Cvc5Term els = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = xp;
  args2[1] = x;
  Cvc5Term the = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  Cvc5Term args3[3] = {cond, els, the};
  Cvc5Term ite = cvc5_mk_term(tm, CVC5_KIND_ITE, 3, args3);

  // define the pre-conditions, transition relations, and post-conditions
  Cvc5Term vars1[1] = {x};
  args2[0] = x;
  args2[1] = zero;
  Cvc5Term pre_f = cvc5_define_fun(slv,
                                   "pre-f",
                                   1,
                                   vars1,
                                   bool_sort,
                                   cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2),
                                   false);
  Cvc5Term vars2[2] = {x, xp};
  Cvc5Term trans_f =
      cvc5_define_fun(slv, "trans-f", 2, vars2, bool_sort, ite, false);
  args2[0] = x;
  args2[1] = ten;
  Cvc5Term post_f = cvc5_define_fun(slv,
                                    "post-f",
                                    1,
                                    vars1,
                                    bool_sort,
                                    cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2),
                                    false);

  // declare the invariant-to-synthesize
  Cvc5Term inv_f = cvc5_synth_fun(slv, "inv-f", 1, vars1, bool_sort);

  cvc5_add_sygus_inv_constraint(slv, inv_f, pre_f, trans_f, post_f);

  // print solutions if available
  if (cvc5_synth_result_has_solution(cvc5_check_synth(slv)))
  {
    // Output should be equivalent to:
    // (
    //   (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
    // )
    Cvc5Term args1[1] = {inv_f};
    const Cvc5Term* sols = cvc5_get_synth_solutions(slv, 1, args1);
    print_synth_solutions(1, args1, sols);
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
