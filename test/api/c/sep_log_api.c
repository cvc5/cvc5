/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew V. Jones
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Two tests to validate the use of the separation logic API.
 *
 * First test validates that we cannot use the API if not using separation
 * logic.
 *
 * Second test validates that the expressions returned from the API are
 * correct and can be interrogated.
 *
 ****************************************************************************/

#include <cvc5/c/cvc5.h>

int main(void)
{
  int res = 0;
  /**
   * Test function to demonstrate the use of, and validate the capability, of
   * obtaining the heap/nil expressions when using separation logic.
   */
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* solver = cvc5_new(tm);

  /* Setup some options for cvc5 */
  cvc5_set_logic(solver, "ALL");
  cvc5_set_option(solver, "produce-models", "true");
  cvc5_set_option(solver, "incremental", "false");

  /* Our integer type */
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);

  /** Declare the separation logic heap types */
  cvc5_declare_sep_heap(solver, int_sort, int_sort);

  /* A "random" constant */
  Cvc5Term random_constant = cvc5_mk_integer_int64(tm, 0xDEADBEEF);

  /* Another random constant */
  Cvc5Term expr_nil_val = cvc5_mk_integer_int64(tm, 0xFBADBEEF);

  /* Our nil term */
  Cvc5Term nil = cvc5_mk_sep_nil(tm, int_sort);

  /* Our SMT constants */
  Cvc5Term x = cvc5_mk_const(tm, int_sort, "x");
  Cvc5Term y = cvc5_mk_const(tm, int_sort, "y");
  Cvc5Term p1 = cvc5_mk_const(tm, int_sort, "p1");
  Cvc5Term p2 = cvc5_mk_const(tm, int_sort, "p2");

  /* Constraints on x and y */
  Cvc5Term args[2] = {x, random_constant};
  Cvc5Term x_eq_const = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);
  args[0] = y;
  args[1] = x;
  Cvc5Term y_gt_x = cvc5_mk_term(tm, CVC5_KIND_GT, 2, args);

  /* Points-to expressions */
  args[0] = p1;
  args[1] = x;
  Cvc5Term p1_to_x = cvc5_mk_term(tm, CVC5_KIND_SEP_PTO, 2, args);
  args[0] = p2;
  args[1] = y;
  Cvc5Term p2_to_y = cvc5_mk_term(tm, CVC5_KIND_SEP_PTO, 2, args);

  /* Heap -- the points-to have to be "starred"! */
  args[0] = p1_to_x;
  args[1] = p2_to_y;
  Cvc5Term heap = cvc5_mk_term(tm, CVC5_KIND_SEP_STAR, 2, args);

  /* Constain "nil" to be something random */
  args[0] = nil;
  args[1] = expr_nil_val;
  Cvc5Term fix_nil = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args);

  /* Add it all to the solver! */
  cvc5_assert_formula(solver, x_eq_const);
  cvc5_assert_formula(solver, y_gt_x);
  cvc5_assert_formula(solver, heap);
  cvc5_assert_formula(solver, fix_nil);

  /*
   * Incremental is disabled due to using separation logic, so don't query
   * twice!
   */
  Cvc5Result r = cvc5_check_sat(solver);

  /* If this is UNSAT, we have an issue; so bail-out */
  if (!cvc5_result_is_sat(r))
  {
    res = -1;
  }
  else
  {
    /* Obtain our separation logic terms from the solver */

    Cvc5Term heap_expr = cvc5_get_value_sep_heap(solver);
    Cvc5Term nil_expr = cvc5_get_value_sep_nil(solver);

    /* If the heap is not a separating conjunction, bail-out */
    if (cvc5_term_get_kind(heap_expr) != CVC5_KIND_SEP_STAR)
    {
      res = -1;
    }
    /* If nil is not a direct equality, bail-out */
    else if (cvc5_term_get_kind(nil_expr) != CVC5_KIND_EQUAL)
    {
      res = -1;
    }
    else
    {
      /* Obtain the values for our "pointers" */
      Cvc5Term val_for_p1 = cvc5_get_value(solver, p1);
      Cvc5Term val_for_p2 = cvc5_get_value(solver, p2);

      /* We need to make sure we find both pointers in the heap */
      bool checked_p1 = false;
      bool checked_p2 = false;

      /* Walk all the children */
      for (size_t i = 0, n = cvc5_term_get_num_children(heap_expr); i < n; i++)
      {
        Cvc5Term child = cvc5_term_get_child(heap_expr, i);
        /* If we don't have a PTO operator, bail-out */
        if (cvc5_term_get_kind(child) != CVC5_KIND_SEP_PTO)
        {
          res = -1;
          break;
        }

        /* Find both sides of the PTO operator */
        Cvc5Term addr = cvc5_get_value(solver, cvc5_term_get_child(child, 0));
        Cvc5Term value = cvc5_get_value(solver, cvc5_term_get_child(child, 1));

        /* If the current address is the value for p1 */
        if (cvc5_term_is_equal(addr, val_for_p1))
        {
          checked_p1 = true;

          /* If it doesn't match the random constant, we have a problem */
          if (cvc5_term_is_disequal(value, random_constant))
          {
            res = -1;
            break;
          }
          continue;
        }

        /* If the current address is the value for p2 */
        if (cvc5_term_is_equal(addr, val_for_p2))
        {
          checked_p2 = true;

          /*
           * Our earlier constraint was that what p2 points to must be *greater*
           * than the random constant -- if we get a value that is LTE, then
           * something has gone wrong!
           */
          if (cvc5_term_get_int64_value(value)
              <= cvc5_term_get_int64_value(random_constant))
          {
            res = -1;
            break;
          }
          continue;
        }

        /*
         * We should only have two addresses in heap, so if we haven't hit the
         * "continue" for p1 or p2, then bail-out
         */
        res = -1;
        break;
      }

      /*
       * If we complete the loop and we haven't validated both p1 and p2, then
       * we have a problem
       */
      if (res == 0)
      {
        if (!checked_p1 || !checked_p2)
        {
          res = -1;
        }
        else
        {
          /* We now get our value for what nil is */
          Cvc5Term value_for_nil =
              cvc5_get_value(solver, cvc5_term_get_child(nil_expr, 1));

          /*
           * The value for nil from the solver should be the value we originally
           * tied nil to
           */
          if (cvc5_term_is_disequal(value_for_nil, expr_nil_val))
          {
            res = -1;
          }
        }
      }
    }
  }

  /* All tests pass! */
  cvc5_delete(solver);
  cvc5_term_manager_delete(tm);
  return res;
}
