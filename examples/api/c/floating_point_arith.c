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
 * An example of solving floating-point problems with cvc5's cpp API.
 *
 * This example shows to create floating-point types, variables and expressions,
 * and how to create rounding mode constants by solving toy problems. The
 * example also shows making special values (such as NaN and +oo) and converting
 * an IEEE 754-2008 bit-vector to a floating-point number.
 */

#include <assert.h>
#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "incremental", "true");
  cvc5_set_option(slv, "produce-models", "true");

  // Make single precision floating-point variables
  Cvc5Sort fp32 = cvc5_mk_fp_sort(tm, 8, 24);
  Cvc5Term a = cvc5_mk_const(tm, fp32, "a");
  Cvc5Term b = cvc5_mk_const(tm, fp32, "b");
  Cvc5Term c = cvc5_mk_const(tm, fp32, "c");
  Cvc5Term d = cvc5_mk_const(tm, fp32, "d");
  Cvc5Term e = cvc5_mk_const(tm, fp32, "e");

  // Rounding mode
  Cvc5Term rm = cvc5_mk_rm(tm, CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN);

  printf("Show that fused multiplication and addition `(fp.fma RM a b c)`\n");
  printf("is different from `(fp.add RM (fp.mul a b) c)`:\n");
  cvc5_push(slv, 1);

  Cvc5Term args4[4] = {rm, a, b, c};
  Cvc5Term fma = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_FMA, 4, args4);
  Cvc5Term args3[3] = {rm, a, b};
  Cvc5Term mul = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_MULT, 3, args3);
  args3[0] = rm;
  args3[1] = mul;
  args3[2] = c;
  Cvc5Term add = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_ADD, 3, args3);
  Cvc5Term args2[2] = {fma, add};
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2));

  Cvc5Result r = cvc5_check_sat(slv);  // result is sat
  assert(cvc5_result_is_sat(r));
  printf("Expect sat: %s\n", cvc5_result_to_string(r));
  printf("Value of `a`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, a)));
  printf("Value of `b`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, b)));
  printf("Value of `c`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, c)));
  printf("Value of `(fp.fma RNE a b c)`: %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, fma)));
  printf("Value of `(fp.add RNE (fp.mul a b) c)`: %s\n\n",
         cvc5_term_to_string(cvc5_get_value(slv, add)));
  cvc5_pop(slv, 1);

  printf("Show that floating-point addition is not associative:\n");
  printf("(a + (b + c)) != ((a + b) + c)\n");
  cvc5_push(slv, 1);

  args3[0] = rm;
  args3[1] = b;
  args3[2] = c;
  Cvc5Term fp_add = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_ADD, 3, args3);
  args3[0] = rm;
  args3[1] = a;
  args3[2] = fp_add;
  Cvc5Term lhs = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_ADD, 3, args3);
  args3[0] = rm;
  args3[1] = a;
  args3[2] = b;
  cvc5_term_release(fp_add);  // optional, not needed anymore so we can release
  fp_add = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_ADD, 3, args3);
  args3[0] = rm;
  args3[1] = fp_add;
  args3[2] = c;
  Cvc5Term rhs = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_ADD, 3, args3);

  args2[0] = lhs;
  args2[1] = rhs;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2));

  cvc5_result_release(r);   // optional, not needed anymore so we can release
  r = cvc5_check_sat(slv);  // result is sat
  assert(cvc5_result_is_sat(r));
  printf("Expect sat: %s\n", cvc5_result_to_string(r));
  printf("Value of `a`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, a)));
  printf("Value of `b`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, b)));
  printf("Value of `c`: %s\n\n", cvc5_term_to_string(cvc5_get_value(slv, c)));

  printf("Now, restrict `a` to be either NaN or positive infinity:\n");
  Cvc5Term nan = cvc5_mk_fp_nan(tm, 8, 24);
  Cvc5Term inf = cvc5_mk_fp_pos_inf(tm, 8, 24);
  args2[0] = a;
  args2[1] = inf;
  Cvc5Term eq1 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = a;
  args2[1] = nan;
  Cvc5Term eq2 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = eq1;
  args2[1] = eq2;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_OR, 2, args2));

  cvc5_result_release(r);   // optional, not needed anymore so we can release
  r = cvc5_check_sat(slv);  // result is sat
  assert(cvc5_result_is_sat(r));
  printf("Expect sat: %s\n", cvc5_result_to_string(r));
  printf("Value of `a`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, a)));
  printf("Value of `b`: %s\n", cvc5_term_to_string(cvc5_get_value(slv, b)));
  printf("Value of `c`: %s\n\n", cvc5_term_to_string(cvc5_get_value(slv, c)));
  cvc5_pop(slv, 1);

  printf("Now, try to find a (normal) floating-point number that rounds\n");
  printf("to different integer values for different rounding modes:\n");
  cvc5_push(slv, 1);

  Cvc5Term rtp = cvc5_mk_rm(tm, CVC5_RM_ROUND_TOWARD_POSITIVE);
  Cvc5Term rtn = cvc5_mk_rm(tm, CVC5_RM_ROUND_TOWARD_NEGATIVE);
  // (_ fp.to_ubv 16)
  uint32_t idxs[1] = {16};
  Cvc5Op op = cvc5_mk_op(tm, CVC5_KIND_FLOATINGPOINT_TO_UBV, 1, idxs);
  args2[0] = rtp;
  args2[1] = d;
  cvc5_term_release(lhs);  // optional, not needed anymore so we can release
  lhs = cvc5_mk_term_from_op(tm, op, 2, args2);
  args2[0] = rtn;
  args2[1] = d;
  cvc5_term_release(rhs);  // optional, not needed anymore so we can release
  rhs = cvc5_mk_term_from_op(tm, op, 2, args2);
  Cvc5Term args1[1] = {d};
  cvc5_assert_formula(
      slv, cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_IS_NORMAL, 1, args1));
  args2[0] = lhs;
  args2[1] = rhs;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2));

  cvc5_result_release(r);   // optional, not needed anymore so we can release
  r = cvc5_check_sat(slv);  // result is sat
  assert(cvc5_result_is_sat(r));
  printf("Expect sat: %s\n\n", cvc5_result_to_string(r));

  printf("Get value of `d` as floating-point, bit-vector and real:\n");

  Cvc5Term val = cvc5_get_value(slv, d);
  printf("Value of `d`: %s\n", cvc5_term_to_string(val));
  printf("Value of `((_ fp.to_ubv 16) RTP d)`: %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, lhs)));
  printf("Value of `((_ fp.to_ubv 16) RTN d)`: %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, rhs)));
  args1[0] = val;
  Cvc5Term real_val = cvc5_get_value(
      slv, cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_TO_REAL, 1, args1));
  printf("Value of `(fp.to_real d)` %s\n\n", cvc5_term_to_string(real_val));
  cvc5_pop(slv, 1);

  printf("Finally, try to find a floating-point number between positive\n");
  printf("zero and the smallest positive floating-point number:\n");
  Cvc5Term zero = cvc5_mk_fp_pos_zero(tm, 8, 24);
  Cvc5Term smallest = cvc5_mk_fp(tm, 8, 24, cvc5_mk_bv_uint64(tm, 32, 1));

  args2[0] = zero;
  args2[1] = e;
  cvc5_term_release(lhs);  // optional, not needed anymore so we can release
  lhs = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_LT, 2, args2);
  args2[0] = e;
  args2[1] = smallest;
  cvc5_term_release(rhs);  // optional, not needed anymore so we can release
  rhs = cvc5_mk_term(tm, CVC5_KIND_FLOATINGPOINT_LT, 2, args2);
  args2[0] = lhs;
  args2[1] = rhs;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_AND, 2, args2));

  cvc5_result_release(r);   // optional, not needed anymore so we can release
  r = cvc5_check_sat(slv);  // result is unsat
  assert(cvc5_result_is_unsat(r));
  printf("Expect unsat: %s\n", cvc5_result_to_string(r));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
