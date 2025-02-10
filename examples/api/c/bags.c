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
 * A simple demonstration of reasoning about bags.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_logic(slv, "ALL");
  // Produce models
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_set_option(slv, "incremental", "true");

  Cvc5Sort bag = cvc5_mk_bag_sort(tm, cvc5_get_string_sort(tm));
  Cvc5Term A = cvc5_mk_const(tm, bag, "A");
  Cvc5Term B = cvc5_mk_const(tm, bag, "B");
  Cvc5Term C = cvc5_mk_const(tm, bag, "C");
  Cvc5Term x = cvc5_mk_const(tm, cvc5_get_string_sort(tm), "x");

  Cvc5Term args[2];

  args[0] = A;
  args[1] = C;
  Cvc5Term interAC = cvc5_mk_term(tm, CVC5_KIND_BAG_INTER_MIN, 2, args);
  args[0] = B;
  args[1] = C;
  Cvc5Term interBC = cvc5_mk_term(tm, CVC5_KIND_BAG_INTER_MIN, 2, args);

  // union disjoint does not distribute over intersection
  {
    args[0] = A;
    args[1] = B;
    Cvc5Term union_disAB =
        cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_DISJOINT, 2, args);

    args[0] = union_disAB;
    args[1] = C;
    Cvc5Term lhs = cvc5_mk_term(tm, CVC5_KIND_BAG_INTER_MIN, 2, args);

    args[0] = interAC;
    args[1] = interBC;
    Cvc5Term rhs = cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_DISJOINT, 2, args);

    args[0] = lhs;
    args[1] = rhs;
    Cvc5Term guess = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);

    Cvc5Term args_not[1] = {guess};
    Cvc5Term not_guess = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args_not);

    Cvc5Term assumptions[1] = {not_guess};
    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(not_guess),
           cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));

    // Note: The const char* returned by cvc5_term_to_string is only valid
    //       until the next call to cvc5_term_to_string. Thus, we cannot
    //       chain calls to this function like this:
    //         printf("%s: %s\n",
    //                cvc5_term_to_string(A),
    //                cvc5_term_to_string(cvc5_get_value(slv, A)));
    //       Instead, we have to split such printf calls into two.
    printf("%s: ", cvc5_term_to_string(A));
    printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, A)));

    printf("%s: ", cvc5_term_to_string(B));
    printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, B)));

    printf("%s: ", cvc5_term_to_string(C));
    printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, C)));

    printf("%s: ", cvc5_term_to_string(lhs));
    printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, lhs)));

    printf("%s: ", cvc5_term_to_string(rhs));
    printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, rhs)));
  }

  // union max distributes over intersection
  {
    args[0] = A;
    args[1] = B;
    Cvc5Term union_maxAB = cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_MAX, 2, args);

    args[0] = union_maxAB;
    args[1] = C;
    Cvc5Term lhs = cvc5_mk_term(tm, CVC5_KIND_BAG_INTER_MIN, 2, args);

    args[0] = interAC;
    args[1] = interBC;
    Cvc5Term rhs = cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_MAX, 2, args);

    args[0] = lhs;
    args[1] = rhs;
    Cvc5Term theorem = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);

    Cvc5Term not_args[1] = {theorem};
    Cvc5Term not_theorem = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, not_args);
    Cvc5Term assumptions[1] = {not_theorem};
    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(not_theorem),
           cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
  }

  // Verify emptbag is a subbag of any bag
  {
    Cvc5Term empty_bag = cvc5_mk_empty_bag(tm, bag);
    args[0] = empty_bag;
    args[1] = A;
    Cvc5Term theorem = cvc5_mk_term(tm, CVC5_KIND_BAG_SUBBAG, 2, args);

    Cvc5Term not_args[1] = {theorem};
    Cvc5Term not_theorem = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, not_args);
    Cvc5Term assumptions[1] = {not_theorem};
    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(not_theorem),
           cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
  }

  // find an element with multiplicity 4 in the disjoint union of
  // ; {|"a", "a", "b", "b", "b"|} and {|"b", "c", "c"|}

  {
    Cvc5Term one = cvc5_mk_integer_int64(tm, 1);
    Cvc5Term two = cvc5_mk_integer_int64(tm, 2);
    Cvc5Term three = cvc5_mk_integer_int64(tm, 3);
    Cvc5Term four = cvc5_mk_integer_int64(tm, 4);

    Cvc5Term a = cvc5_mk_string(tm, "a", false);
    Cvc5Term b = cvc5_mk_string(tm, "b", false);
    Cvc5Term c = cvc5_mk_string(tm, "c", false);

    args[0] = a;
    args[1] = two;
    Cvc5Term bag_a_2 = cvc5_mk_term(tm, CVC5_KIND_BAG_MAKE, 2, args);

    args[0] = b;
    args[1] = three;
    Cvc5Term bag_b_3 = cvc5_mk_term(tm, CVC5_KIND_BAG_MAKE, 2, args);

    args[0] = b;
    args[1] = one;
    Cvc5Term bag_b_1 = cvc5_mk_term(tm, CVC5_KIND_BAG_MAKE, 2, args);

    args[0] = c;
    args[1] = two;
    Cvc5Term bag_c_2 = cvc5_mk_term(tm, CVC5_KIND_BAG_MAKE, 2, args);

    args[0] = bag_a_2;
    args[1] = bag_b_3;
    Cvc5Term bag_a_2_b_3 =
        cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_DISJOINT, 2, args);

    args[0] = bag_b_1;
    args[1] = bag_c_2;
    Cvc5Term bag_b_1_c_2 =
        cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_DISJOINT, 2, args);

    args[0] = bag_a_2_b_3;
    args[1] = bag_b_1_c_2;
    Cvc5Term union_disjoint =
        cvc5_mk_term(tm, CVC5_KIND_BAG_UNION_DISJOINT, 2, args);

    args[0] = x;
    args[1] = union_disjoint;
    Cvc5Term count_x = cvc5_mk_term(tm, CVC5_KIND_BAG_COUNT, 2, args);

    args[0] = four;
    args[1] = count_x;
    Cvc5Term e = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);

    Cvc5Term assumptions[1] = {e};
    Cvc5Result result = cvc5_check_sat_assuming(slv, 1, assumptions);

    printf("cvc5 reports: %s is %s.\n",
           cvc5_term_to_string(e),
           cvc5_result_to_string(result));

    if (cvc5_result_is_sat(result))
    {
      printf("%s: ", cvc5_term_to_string(x));
      printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, x)));
    }
  }

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
