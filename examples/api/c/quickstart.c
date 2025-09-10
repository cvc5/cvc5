/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the API capabilities of cvc5.
 *
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

int32_t gcd(int32_t a, int32_t b)
{
  int32_t remainder = a % b;

  if (remainder == 0)
  {
    return b;
  }

  return gcd(b, remainder);
}

int main()
{
  // Create a term manager
  //! [docs-c-quickstart-0 start]
  Cvc5TermManager* tm = cvc5_term_manager_new();
  //! [docs-c-quickstart-0 end]
  // Create a solver
  //! [docs-c-quickstart-1 start]
  Cvc5* slv = cvc5_new(tm);
  //! [docs-c-quickstart-1 end]

  // We will ask the solver to produce models and unsat cores,
  // hence these options should be turned on.
  //! [docs-c-quickstart-2 start]
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_set_option(slv, "produce-unsat-cores", "true");
  //! [docs-c-quickstart-2 end]

  // The simplest way to set a logic for the solver is to choose "ALL".
  // This enables all logics in the solver.
  // Alternatively, "QF_ALL" enables all logics without quantifiers.
  // To optimize the solver's behavior for a more specific logic,
  // use the logic name, e.g. "QF_BV" or "QF_AUFBV".

  // Set the logic
  //! [docs-c-quickstart-3 start]
  cvc5_set_logic(slv, "ALL");
  //! [docs-c-quickstart-3 end]

  // In this example, we will define constraints over reals and integers.
  // Hence, we first obtain the corresponding sorts.
  //! [docs-c-quickstart-4 start]
  Cvc5Sort real_sort = cvc5_get_real_sort(tm);
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  //! [docs-c-quickstart-4 end]

  // x and y will be real variables, while a and b will be integer variables.
  // Formally, their cpp type is Term,
  // and they are called "constants" in SMT jargon:
  //! [docs-c-quickstart-5 start]
  Cvc5Term x = cvc5_mk_const(tm, real_sort, "x");
  Cvc5Term y = cvc5_mk_const(tm, real_sort, "y");
  Cvc5Term a = cvc5_mk_const(tm, int_sort, "a");
  Cvc5Term b = cvc5_mk_const(tm, int_sort, "b");
  //! [docs-c-quickstart-5 end]

  // Our constraints regarding x and y will be:
  //
  //   (1)  0 < x
  //   (2)  0 < y
  //   (3)  x + y < 1
  //   (4)  x <= y
  //

  //! [docs-c-quickstart-6 start]
  // Formally, constraints are also terms. Their sort is Boolean.
  // We will construct these constraints gradually,
  // by defining each of their components.
  // We start with the constant numerals 0 and 1:
  Cvc5Term zero = cvc5_mk_real_int64(tm, 0);
  Cvc5Term one = cvc5_mk_real_int64(tm, 1);

  // Next, we construct the term x + y
  Cvc5Term args2[2] = {x, y};
  Cvc5Term x_plus_y = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);

  // Now we can define the constraints.
  // They use the operators +, <=, and <.
  // In the API, these are denoted by ADD, LEQ, and LT.
  // A list of available operators is available in:
  // src/api/cpp/cvc5_kind.h
  args2[0] = zero;
  args2[1] = x;
  Cvc5Term constraint1 = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);
  args2[1] = y;
  Cvc5Term constraint2 = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);
  args2[0] = x_plus_y;
  args2[1] = one;
  Cvc5Term constraint3 = cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2);
  args2[0] = x;
  args2[1] = y;
  Cvc5Term constraint4 = cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2);

  // Now we assert the constraints to the solver.
  cvc5_assert_formula(slv, constraint1);
  cvc5_assert_formula(slv, constraint2);
  cvc5_assert_formula(slv, constraint3);
  cvc5_assert_formula(slv, constraint4);
  //! [docs-c-quickstart-6 end]

  // Check if the formula is satisfiable, that is,
  // are there real values for x and y that satisfy all the constraints?
  //! [docs-c-quickstart-7 start]
  Cvc5Result r = cvc5_check_sat(slv);
  //! [docs-c-quickstart-7 end]

  // The result is either SAT, UNSAT, or UNKNOWN.
  // In this case, it is SAT.
  //! [docs-c-quickstart-8 start]
  printf("expected: sat\n");
  printf("result: %s\n", cvc5_result_to_string(r));
  //! [docs-c-quickstart-8 end]

  // We can get the values for x and y that satisfy the constraints.
  //! [docs-c-quickstart-9 start]
  Cvc5Term x_val = cvc5_get_value(slv, x);
  Cvc5Term y_val = cvc5_get_value(slv, y);
  //! [docs-c-quickstart-9 end]

  // It is also possible to get values for compound terms,
  // even if those did not appear in the original formula.
  //! [docs-c-quickstart-10 start]
  args2[0] = x;
  args2[1] = y;
  Cvc5Term x_minus_y = cvc5_mk_term(tm, CVC5_KIND_SUB, 2, args2);
  Cvc5Term x_minus_y_val = cvc5_get_value(slv, x_minus_y);
  //! [docs-c-quickstart-10 end]

  // We can now obtain the string representations of the values.
  //! [docs-c-quickstart-11 start]
  // Note: The const char* returned by cvc5_term_get_real_value is only valid
  //       until the next call to this function.
  char* x_str = strdup(cvc5_term_get_real_value(x_val));
  char* y_str = strdup(cvc5_term_get_real_value(y_val));
  char* x_minus_y_str = strdup(cvc5_term_get_real_value(x_minus_y_val));

  printf("value for x: %s\n", x_str);
  printf("value for y: %s\n", y_str);
  printf("value for x - y: %s\n", x_minus_y_str);

  free(y_str);
  free(x_str);
  free(x_minus_y_str);

  // Alternatively, you can directly print the value strings without
  // copying them first:
  printf("value for x: %s\n", cvc5_term_get_real_value(x_val));
  printf("value for y: %s\n", cvc5_term_get_real_value(y_val));
  printf("value for x - y: %s\n", cvc5_term_get_real_value(x_minus_y_val));
  //! [docs-c-quickstart-11 end]

  //! [docs-c-quickstart-12 start]
  // Further, we can convert the values to cpp types
  int64_t x_num;
  uint64_t x_den;
  cvc5_term_get_real64_value(x_val, &x_num, &x_den);
  int64_t y_num;
  uint64_t y_den;
  cvc5_term_get_real64_value(y_val, &y_num, &y_den);
  int64_t x_minus_y_num;
  uint64_t x_minus_y_den;
  cvc5_term_get_real64_value(x_minus_y_val, &x_minus_y_num, &x_minus_y_den);

  printf("value for x: %" PRId64 "/%" PRIu64 "\n", x_num, x_den);
  printf("value for y: %" PRId64 "/%" PRIu64 "\n", y_num, y_den);
  printf("value for x - y: %" PRId64 "/%" PRIu64 "\n", x_minus_y_num, x_minus_y_den);
  //! [docs-c-quickstart-12 end]

  // Another way to independently compute the value of x - y would be
  // to perform the (rational) arithmetic manually.
  // However, for more complex terms,
  // it is easier to let the solver do the evaluation.
  //! [docs-c-quickstart-13 start]
  int64_t x_minus_y_num_computed = x_num * y_den - x_den * y_num;
  uint64_t x_minus_y_den_computed = x_den * y_den;
  uint64_t g = gcd(x_minus_y_num_computed, x_minus_y_den_computed);
  x_minus_y_num_computed = x_minus_y_num_computed / g;
  x_minus_y_den_computed = x_minus_y_den_computed / g;
  if (x_minus_y_num_computed == x_minus_y_num
      && x_minus_y_den_computed == x_minus_y_den)
  {
    printf("computed correctly\n");
  }
  else
  {
    printf("computed incorrectly\n");
  }
  //! [docs-c-quickstart-13 end]

  // Next, we will check satisfiability of the same formula,
  // only this time over integer variables a and b.

  // We start by resetting assertions added to the solver.
  //! [docs-c-quickstart-14 start]
  cvc5_reset_assertions(slv);
  //! [docs-c-quickstart-14 end]

  // Next, we assert the same assertions above with integers.
  // This time, we inline the construction of terms
  // to the assertion command.
  //! [docs-c-quickstart-15 start]
  args2[0] = cvc5_mk_integer_int64(tm, 0);
  args2[1] = a;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2));
  args2[1] = b;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2));
  args2[0] = a;
  args2[1] = b;
  Cvc5Term add = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args2);
  args2[0] = add;
  args2[1] = cvc5_mk_integer_int64(tm, 1);
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LT, 2, args2));
  args2[0] = a;
  args2[1] = b;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, args2));
  //! [docs-c-quickstart-15 end]

  // We check whether the revised assertion is satisfiable.
  //! [docs-c-quickstart-16 start]
  cvc5_result_release(r);  // optional, not needed anymore so we can release
  r = cvc5_check_sat(slv);
  //! [docs-c-quickstart-16 end]

  // This time the formula is unsatisfiable
  //! [docs-c-quickstart-17 start]
  printf("expected: unsat\n");
  printf("result: %s\n", cvc5_result_to_string(r));
  //! [docs-c-quickstart-17 end]

  // We can query the solver for an unsatisfiable core, i.e., a subset
  // of the assertions that is already unsatisfiable.
  //! [docs-c-quickstart-18 start]
  size_t size;
  const Cvc5Term* unsat_core = cvc5_get_unsat_core(slv, &size);
  printf("unsat core size: %zu\n", size);
  printf("unsat core: \n");
  for (size_t i = 0; i < size; i++)
  {
    printf("%s\n", cvc5_term_to_string(unsat_core[i]));
  }
  //! [docs-c-quickstart-18 end]

  // Delete solver instance.
  //! [docs-c-quickstart-19 start]
  cvc5_delete(slv);
  //! [docs-c-quickstart-19 end]

  // Delete term manager instance.
  //! [docs-c-quickstart-20 start]
  cvc5_term_manager_delete(tm);
  //! [docs-c-quickstart-20 end]
  return 0;
}
