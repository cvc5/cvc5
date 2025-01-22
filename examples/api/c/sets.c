/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about sets via the C API.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  // Optionally, set the logic. We need at least UF for equality predicate,
  // integers (LIA) and sets (FS).
  cvc5_set_logic(slv, "QF_UFLIAFS");

  // Produce models
  cvc5_set_option(slv, "produce-models", "true");

  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  Cvc5Sort set_sort = cvc5_mk_set_sort(tm, int_sort);

  // Verify union distributions over intersection
  // (A union B) intersection C = (A intersection C) union (B intersection C)
  {
    Cvc5Term A = cvc5_mk_const(tm, set_sort, "A");
    Cvc5Term B = cvc5_mk_const(tm, set_sort, "B");
    Cvc5Term C = cvc5_mk_const(tm, set_sort, "C");

    Cvc5Term args2[2] = {A, B};
    Cvc5Term union_AB = cvc5_mk_term(tm, CVC5_KIND_SET_UNION, 2, args2);
    args2[0] = union_AB;
    args2[1] = C;
    Cvc5Term lhs = cvc5_mk_term(tm, CVC5_KIND_SET_INTER, 2, args2);

    args2[0] = A;
    args2[1] = C;
    Cvc5Term inter_AC = cvc5_mk_term(tm, CVC5_KIND_SET_INTER, 2, args2);
    args2[0] = B;
    args2[1] = C;
    Cvc5Term inter_BC = cvc5_mk_term(tm, CVC5_KIND_SET_INTER, 2, args2);
    args2[0] = inter_AC;
    args2[1] = inter_BC;
    Cvc5Term rhs = cvc5_mk_term(tm, CVC5_KIND_SET_UNION, 2, args2);

    args2[0] = lhs;
    args2[1] = rhs;
    Cvc5Term theorem = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

    Cvc5Term args1[1] = {theorem};
    Cvc5Term assumptions[1] = {cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1)};
    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(theorem),
           cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
    // optional, not needed anymore so we can release
    cvc5_term_release(A);
    cvc5_term_release(B);
    cvc5_term_release(C);
    cvc5_term_release(union_AB);
    cvc5_term_release(inter_AC);
    cvc5_term_release(inter_BC);
    cvc5_term_release(lhs);
    cvc5_term_release(rhs);
    cvc5_term_release(theorem);
  }

  // Verify emptset is a subset of any set
  {
    Cvc5Term A = cvc5_mk_const(tm, set_sort, "A");
    Cvc5Term empty_set = cvc5_mk_empty_set(tm, set_sort);

    Cvc5Term args2[2] = {empty_set, A};
    Cvc5Term theorem = cvc5_mk_term(tm, CVC5_KIND_SET_SUBSET, 2, args2);

    Cvc5Term args1[1] = {theorem};
    Cvc5Term assumptions[1] = {cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1)};
    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(theorem),
           cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
    // optional, not needed anymore so we can release
    cvc5_term_release(A);
    cvc5_term_release(theorem);
  }

  // Find me an element in {1, 2} intersection {2, 3}, if there is one.
  {
    Cvc5Term one = cvc5_mk_integer_int64(tm, 1);
    Cvc5Term two = cvc5_mk_integer_int64(tm, 2);
    Cvc5Term three = cvc5_mk_integer_int64(tm, 3);

    Cvc5Term args1[1] = {one};
    Cvc5Term sing_one = cvc5_mk_term(tm, CVC5_KIND_SET_SINGLETON, 1, args1);
    args1[0] = two;
    Cvc5Term sing_two = cvc5_mk_term(tm, CVC5_KIND_SET_SINGLETON, 1, args1);
    args1[0] = three;
    Cvc5Term sing_three = cvc5_mk_term(tm, CVC5_KIND_SET_SINGLETON, 1, args1);
    Cvc5Term args2[2] = {sing_one, sing_two};
    Cvc5Term one_two = cvc5_mk_term(tm, CVC5_KIND_SET_UNION, 2, args2);
    args2[0] = sing_two;
    args2[1] = sing_three;
    Cvc5Term two_three = cvc5_mk_term(tm, CVC5_KIND_SET_UNION, 2, args2);
    args2[0] = one_two;
    args2[1] = two_three;
    Cvc5Term inter = cvc5_mk_term(tm, CVC5_KIND_SET_INTER, 2, args2);

    Cvc5Term x = cvc5_mk_const(tm, int_sort, "x");
    args2[0] = x;
    args2[1] = inter;
    Cvc5Term e = cvc5_mk_term(tm, CVC5_KIND_SET_MEMBER, 2, args2);

    Cvc5Term assumptions[1] = {e};
    Cvc5Result result = cvc5_check_sat_assuming(slv, 1, assumptions);
    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(e),
           cvc5_result_to_string(result));

    if (cvc5_result_is_sat(result))
    {
      printf("For instance, %s is a member.\n",
             cvc5_term_to_string(cvc5_get_value(slv, x)));
    }
  }
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
