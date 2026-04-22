/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A demonstration of the SyGuS 2.1 weight API.
 *
 * Synthesize 3*x using only `+` (weight 1) and `*` (weight 31), constrained
 * to have a total `w` weight of 2. The expected solution is (+ x (+ x x)).
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
  cvc5_set_logic(slv, "NIA");

  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);

  // declare input variables for the function-to-synthesize
  Cvc5Term x = cvc5_mk_var(tm, int_sort, "x");

  // declare the grammar non-terminal
  Cvc5Term start = cvc5_mk_var(tm, int_sort, "Start");

  // define the rules
  Cvc5Term zero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(tm, 1);
  Cvc5Term two = cvc5_mk_integer_int64(tm, 2);
  Cvc5Term three = cvc5_mk_integer_int64(tm, 3);
  Cvc5Term thirty_one = cvc5_mk_integer_int64(tm, 31);

  Cvc5Term args2[2] = {start, start};
  Cvc5Term plus = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);
  Cvc5Term mult = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, args2);

  // declare a weight attribute with the default value of 0
  Cvc5Weight w = cvc5_declare_weight(slv, "w");

  // create the grammar object
  Cvc5Term b[1] = {x};
  Cvc5Term s[1] = {start};
  Cvc5Grammar g = cvc5_mk_grammar(slv, 1, b, 1, s);

  // bind each non-terminal to its rules
  Cvc5Term rules[4] = {zero, one, three, x};
  cvc5_grammar_add_rules(g, start, 4, rules);

  Cvc5Weight wkey[1] = {w};
  Cvc5Term add_weight[1] = {one};
  cvc5_grammar_add_rule_with_weights(g, start, plus, 1, wkey, add_weight);

  Cvc5Term mult_weight[1] = {thirty_one};
  cvc5_grammar_add_rule_with_weights(g, start, mult, 1, wkey, mult_weight);

  // declare the function-to-synthesize
  Cvc5Term f = cvc5_synth_fun_with_grammar(slv, "f", 1, b, int_sort, g);

  // declare universal variables
  Cvc5Term var_x = cvc5_declare_sygus_var(slv, "x", int_sort);

  // build (f x) and (* 3 x)
  Cvc5Term apply_args[2] = {f, var_x};
  Cvc5Term f_of_x = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, apply_args);

  Cvc5Term three_x_args[2] = {three, var_x};
  Cvc5Term three_x = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, three_x_args);

  // add the semantic constraint: (= (f x) (* 3 x))
  Cvc5Term eq_args[2] = {f_of_x, three_x};
  cvc5_add_sygus_constraint(slv, cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, eq_args));

  // declare the weight symbol (_ w f)
  Cvc5Term wF = cvc5_mk_weight_symbol(slv, w, f);

  // add the weight constraint: (= (_ w f) 2)
  Cvc5Term weq_args[2] = {wF, two};
  cvc5_add_sygus_constraint(slv,
                            cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, weq_args));

  // print the solution if available
  if (cvc5_synth_result_has_solution(cvc5_check_synth(slv)))
  {
    // Output should be equivalent to:
    // (
    //   (define-fun f ((x Int)) Int (+ x (+ x x)))
    // )
    Cvc5Term terms[1] = {f};
    const Cvc5Term* sols = cvc5_get_synth_solutions(slv, 1, terms);
    print_synth_solutions(1, terms, sols);
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
