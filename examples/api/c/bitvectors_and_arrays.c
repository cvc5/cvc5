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
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector and array solvers.
 *
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_set_logic(slv, "QF_ABV");

  // Consider the following code (where size is some previously defined
  // constant):
  //
  //
  //   Assert (current_array[0] > 0);
  //   for (unsigned i = 1; i < k; ++i) {
  //     current_array[i] = 2 * current_array[i - 1];
  //     Assert (current_array[i-1] < current_array[i]);
  //     }
  //
  // We want to check whether the assertion in the body of the for loop holds
  // throughout the loop.

  // Setting up the problem parameters
  uint32_t k = 4;           // number of unrollings (should be a power of 2)
  uint32_t index_size = 2;  // size of the index, must be log2(k)

  // Sorts
  Cvc5Sort elem_sort = cvc5_mk_bv_sort(tm, 32);
  Cvc5Sort index_sort = cvc5_mk_bv_sort(tm, index_size);
  Cvc5Sort arr_sort = cvc5_mk_array_sort(tm, index_sort, elem_sort);

  // Variables
  Cvc5Term cur_arr = cvc5_mk_const(tm, arr_sort, "current_array");

  // Making a bit-vector constant
  Cvc5Term zero = cvc5_mk_bv_uint64(tm, index_size, 0);

  // Asserting that current_array[0] > 0
  Cvc5Term args2[2] = {cur_arr, zero};
  Cvc5Term cur_arr0 = cvc5_mk_term(tm, CVC5_KIND_SELECT, 2, args2);
  args2[0] = cur_arr0;
  args2[1] = cvc5_mk_bv_uint64(tm, 32, 0);
  Cvc5Term cur_arr0_gt_0 = cvc5_mk_term(tm, CVC5_KIND_BITVECTOR_SGT, 2, args2);
  cvc5_assert_formula(slv, cur_arr0_gt_0);

  // Building the assertions in the loop unrolling
  Cvc5Term index = cvc5_mk_bv_uint64(tm, index_size, 0);
  args2[0] = cur_arr;
  args2[1] = index;
  Cvc5Term old_cur = cvc5_mk_term(tm, CVC5_KIND_SELECT, 2, args2);
  Cvc5Term two = cvc5_mk_bv_uint64(tm, 32, 2);

  uint32_t size = k - 1;
  Cvc5Term assertions[size];
  for (uint32_t i = 1; i < k; ++i)
  {
    index = cvc5_mk_bv_uint64(tm, index_size, i);
    args2[0] = two;
    args2[1] = old_cur;
    Cvc5Term new_cur = cvc5_mk_term(tm, CVC5_KIND_BITVECTOR_MULT, 2, args2);
    // current[i] = 2 * current[i-1]
    Cvc5Term args3[3] = {cur_arr, index, new_cur};
    cur_arr = cvc5_mk_term(tm, CVC5_KIND_STORE, 3, args3);
    // current[i-1] < current [i]
    args2[0] = old_cur;
    args2[1] = new_cur;
    Cvc5Term cur_slt_new_cur =
        cvc5_mk_term(tm, CVC5_KIND_BITVECTOR_SLT, 2, args2);
    assertions[i - 1] = cur_slt_new_cur;
    args2[0] = cur_arr;
    args2[1] = index;
    old_cur = cvc5_mk_term(tm, CVC5_KIND_SELECT, 2, args2);
  }

  Cvc5Term args1[1] = {cvc5_mk_term(tm, CVC5_KIND_AND, size, assertions)};
  Cvc5Term query = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);

  printf("Asserting %s to cvc5\n", cvc5_term_to_string(query));
  cvc5_assert_formula(slv, query);
  printf("Expect sat.\n");
  printf("cvc5: %s\n", cvc5_result_to_string(cvc5_check_sat(slv)));

  // Getting the model
  printf("The satisfying model is:\n");
  printf("  current_array = %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, cur_arr)));
  printf("  current_array[0] = %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, cur_arr0)));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
