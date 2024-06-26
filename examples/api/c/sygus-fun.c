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
 * A simple demonstration of how to use the Sygus API to synthesize max and min
 * functions.
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

  // declare input variables for the functions-to-synthesize
  Cvc5Term x = cvc5_mk_var(tm, int_sort, "x");
  Cvc5Term y = cvc5_mk_var(tm, int_sort, "y");

  // declare the grammar non-terminals
  Cvc5Term start = cvc5_mk_var(tm, int_sort, "Start");
  Cvc5Term start_bool = cvc5_mk_var(tm, bool_sort, "StartBool");

  // define the rules
  Cvc5Term zero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(tm, 1);

  Cvc5Term args2[2] = {start, start};
  Cvc5Term plus = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);
  Cvc5Term minus = cvc5_mk_term(tm, CVC5_KIND_SUB, 2, args2);
  Cvc5Term args3[3] = {start_bool, start, start};
  Cvc5Term ite = cvc5_mk_term(tm, CVC5_KIND_ITE, 3, args3);

  args2[0] = start_bool;
  args2[1] = start_bool;
  Cvc5Term And = cvc5_mk_term(tm, CVC5_KIND_AND, 2, args2);
  Cvc5Term args1[1] = {start_bool};
  Cvc5Term Not = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);
  args2[0] = start;
  args2[1] = start;
  Cvc5Term leq = cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2);

  // create the grammar object
  Cvc5Term b[2] = {x, y};
  Cvc5Term s[2] = {start, start_bool};
  Cvc5Grammar g = cvc5_mk_grammar(slv, 2, b, 2, s);

  // bind each non-terminal to its rules
  Cvc5Term rules7[7] = {zero, one, x, y, plus, minus, ite};
  cvc5_grammar_add_rules(g, start, 7, rules7);
  Cvc5Term rules3[3] = {And, Not, leq};
  cvc5_grammar_add_rules(g, start_bool, 3, rules3);

  // declare the functions-to-synthesize. Optionally, provide the grammar
  // constraints
  Cvc5Term max = cvc5_synth_fun_with_grammar(slv, "max", 2, b, int_sort, g);
  Cvc5Term min = cvc5_synth_fun(slv, "min", 2, b, int_sort);

  // declare universal variables.
  Cvc5Term var_x = cvc5_declare_sygus_var(slv, "x", int_sort);
  Cvc5Term var_y = cvc5_declare_sygus_var(slv, "y", int_sort);

  args3[0] = max;
  args3[1] = var_x;
  args3[2] = var_y;
  Cvc5Term max_x_y = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, args3);
  args3[0] = min;
  Cvc5Term min_x_y = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, args3);

  // add semantic constraints
  // (constraint (>= (max x y) x))
  args2[0] = max_x_y;
  args2[1] = var_x;
  cvc5_add_sygus_constraint(slv, cvc5_mk_term(tm, CVC5_KIND_GEQ, 2, args2));

  // (constraint (>= (max x y) y))
  args2[1] = var_y;
  cvc5_add_sygus_constraint(slv, cvc5_mk_term(tm, CVC5_KIND_GEQ, 2, args2));

  // (constraint (or (= x (max x y))
  //                 (= y (max x y))))
  args2[0] = max_x_y;
  args2[1] = var_x;
  Cvc5Term lhs = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = max_x_y;
  args2[1] = var_y;
  Cvc5Term rhs = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = lhs;
  args2[1] = rhs;
  cvc5_add_sygus_constraint(slv, cvc5_mk_term(tm, CVC5_KIND_OR, 2, args2));

  // (constraint (= (+ (max x y) (min x y))
  //                (+ x y)))
  args2[0] = max_x_y;
  args2[1] = min_x_y;
  cvc5_term_release(lhs);  // optional, not needed anymore so we can release
  lhs = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);
  args2[0] = var_x;
  args2[1] = var_y;
  cvc5_term_release(rhs);  // optional, not needed anymore so we can release
  rhs = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);
  args2[0] = lhs;
  args2[1] = rhs;
  cvc5_add_sygus_constraint(slv, cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2));

  // print solutions if available
  if (cvc5_synth_result_has_solution(cvc5_check_synth(slv)))
  {
    // Output should be equivalent to:
    // (
    //   (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
    //   (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
    // )
    args2[0] = max;
    args2[1] = min;
    const Cvc5Term* sols = cvc5_get_synth_solutions(slv, 2, args2);
    print_synth_solutions(2, args2, sols);
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
