/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector solver.
 *
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_logic(slv, "QF_BV");

  // The following example has been adapted from the book A Hacker's Delight by
  // Henry S. Warren.
  //
  // Given a variable x that can only have two values, a or b. We want to
  // assign to x a value other than the current one. The straightforward code
  // to do that is:
  //
  //(0) if (x == a ) x = b;
  //    else x = a;
  //
  // Two more efficient yet equivalent methods are:
  //
  //(1) x = a ⊕ b ⊕ x;
  //
  //(2) x = a + b - x;
  //
  // We will use cvc5 to prove that the three pieces of code above are all
  // equivalent by encoding the problem in the bit-vector theory.

  // Creating a bit-vector type of width 32
  Cvc5Sort bv32 = cvc5_mk_bv_sort(tm, 32);

  // Variables
  Cvc5Term x = cvc5_mk_const(tm, bv32, "x");
  Cvc5Term a = cvc5_mk_const(tm, bv32, "a");
  Cvc5Term b = cvc5_mk_const(tm, bv32, "b");

  Cvc5Term args2[2];

  // First encode the assumption that x must be equal to a or b
  args2[0] = x;
  args2[1] = a;
  Cvc5Term x_eq_a = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = x;
  args2[1] = b;
  Cvc5Term x_eq_b = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = x_eq_a;
  args2[1] = x_eq_b;
  Cvc5Term assumption = cvc5_mk_term(tm, CVC5_KIND_OR, 2, args2);

  // Assert the assumption
  cvc5_assert_formula(slv, assumption);

  // Introduce a new variable for the new value of x after assignment.
  // x after executing code (0)
  Cvc5Term new_x = cvc5_mk_const(tm, bv32, "new_x");
  // x after executing code (1) or (2)
  Cvc5Term new_x_ = cvc5_mk_const(tm, bv32, "new_x_");

  // Encoding code (0)
  // new_x = x == a ? b : a;
  Cvc5Term args3[3] = {x_eq_a, b, a};
  Cvc5Term ite = cvc5_mk_term(tm, CVC5_KIND_ITE, 3, args3);
  args2[0] = new_x;
  args2[1] = ite;
  Cvc5Term assignment0 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // Assert the encoding of code (0)
  printf("Asserting %s to cvc5\n", cvc5_term_to_string(assignment0));
  cvc5_assert_formula(slv, assignment0);
  printf("Pushing a new context.\n");
  cvc5_push(slv, 1);

  // Encoding code (1)
  // new_x_ = a xor b xor x
  args3[0] = a;
  args3[1] = b;
  args3[2] = x;
  Cvc5Term a_xor_b_xor_x = cvc5_mk_term(tm, CVC5_KIND_BITVECTOR_XOR, 3, args3);
  args2[0] = new_x_;
  args2[1] = a_xor_b_xor_x;
  Cvc5Term assignment1 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // Assert encoding to cvc5 in current context;
  printf("Asserting %s to cvc5\n", cvc5_term_to_string(assignment1));
  cvc5_assert_formula(slv, assignment1);
  args2[0] = new_x;
  args2[1] = new_x_;
  Cvc5Term new_x_eq_new_x_ = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  Cvc5Term args1[1] = {new_x_eq_new_x_};
  Cvc5Term not_new_x_eq_new_x_ = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);
  printf(" Check sat assuming: %s\n", cvc5_term_to_string(not_new_x_eq_new_x_));
  printf(" Expect UNSAT.\n");

  Cvc5Term assumptions[1] = {not_new_x_eq_new_x_};
  printf(" cvc5: %s\n",
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
  printf(" Popping context.\n");
  cvc5_pop(slv, 1);

  // Encoding code (2)
  // new_x_ = a + b - x
  args2[0] = a;
  args2[1] = b;
  Cvc5Term a_plus_b = cvc5_mk_term(tm, CVC5_KIND_BITVECTOR_ADD, 2, args2);
  args2[0] = a_plus_b;
  args2[1] = x;
  Cvc5Term a_plus_b_minus_x =
      cvc5_mk_term(tm, CVC5_KIND_BITVECTOR_SUB, 2, args2);
  args2[0] = new_x_;
  args2[1] = a_plus_b_minus_x;
  Cvc5Term assignment2 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // Assert encoding to cvc5 in current context;
  printf("Asserting %s to cvc5\n", cvc5_term_to_string(assignment2));
  cvc5_assert_formula(slv, assignment2);

  printf(" Check sat assuming: %s\n", cvc5_term_to_string(not_new_x_eq_new_x_));
  printf(" Expect UNSAT.\n");
  printf(" cvc5: %s\n",
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));

  args2[0] = x;
  args2[1] = x;
  Cvc5Term x_neq_x = cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2);

  args2[0] = new_x_eq_new_x_;
  args2[1] = x_neq_x;
  Cvc5Term query = cvc5_mk_term(tm, CVC5_KIND_AND, 2, args2);
  args1[0] = query;
  Cvc5Term not_query = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);
  printf(" Check sat assuming: %s\n", cvc5_term_to_string(not_query));
  printf(" Expect SAT.\n");
  assumptions[0] = not_query;
  printf(" cvc5: %s\n",
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));

  // Assert that a is odd
  uint32_t idxs[2] = {0, 0};
  Cvc5Op extract_op = cvc5_mk_op(tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs);
  args1[0] = a;
  Cvc5Term lsb_of_a = cvc5_mk_term_from_op(tm, extract_op, 1, args1);
  printf("Sort of %s is %s\n",
         cvc5_term_to_string(lsb_of_a),
         cvc5_sort_to_string(cvc5_term_get_sort(lsb_of_a)));
  args2[0] = lsb_of_a;
  args2[1] = cvc5_mk_bv_uint64(tm, 1, 1);
  Cvc5Term a_odd = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  printf("Assert %s\n", cvc5_term_to_string(a_odd));
  printf("Check satisfiability.\n");
  cvc5_assert_formula(slv, a_odd);
  printf(" Expect sat.\n");
  printf(" cvc5: %s\n", cvc5_result_to_string(cvc5_check_sat(slv)));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
