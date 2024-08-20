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
 * An example of using inductive datatypes in cvc5.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

void test(Cvc5TermManager* tm, Cvc5* slv, Cvc5Sort cons_list_sort)
{
  // Now our old "cons_list_decl" is useless--the relevant information
  // has been copied out, so we can throw that spec away.  We can get
  // the complete spec for the datatype from the DatatypeSort, and
  // this Datatype object has constructor symbols (and others) filled in.

  Cvc5Datatype cons_list = cvc5_sort_get_datatype(cons_list_sort);

  // t = cons 0 nil
  //
  // Here, cvc5_dt_cons_get_constructor_by_name(cons_list, "cons") gives you
  // the Cvc5DatatypeConstructor. Note that "nil" is a constructor too, so it
  // needs to be applied with CVC5_KIND_APPLY_CONSTRUCTOR, even though it has
  // no arguments.
  Cvc5Term nil_term =
      cvc5_dt_cons_get_term(cvc5_dt_get_constructor_by_name(cons_list, "nil"));
  Cvc5DatatypeConstructor cons =
      cvc5_dt_get_constructor_by_name(cons_list, "cons");
  Cvc5Term cons_term = cvc5_dt_cons_get_term(cons);
  Cvc5Term args1[1] = {nil_term};
  Cvc5Term args3[3] = {cons_term,
                       cvc5_mk_integer_int64(tm, 0),
                       cvc5_mk_term(tm, CVC5_KIND_APPLY_CONSTRUCTOR, 1, args1)};
  Cvc5Term t = cvc5_mk_term(tm, CVC5_KIND_APPLY_CONSTRUCTOR, 3, args3);

  printf("t is %s\n", cvc5_term_to_string(t));
  printf("sort of cons is %s\n",
         cvc5_sort_to_string(cvc5_term_get_sort(cons_term)));
  printf("sort of nil is %s\n",
         cvc5_sort_to_string(cvc5_term_get_sort(nil_term)));

  // t2 = head(cons 0 nil), and of course this can be evaluated
  //
  // Here we first get the DatatypeConstructor for cons (with
  // cvc5_dt_cons_get_constructor_by_name(cons_list, "cons") in order to get
  // the "head" selector symbol to apply.
  Cvc5DatatypeSelector head = cvc5_dt_cons_get_selector_by_name(cons, "head");
  Cvc5Term args2[2] = {cvc5_dt_sel_get_term(head), t};
  Cvc5Term t2 = cvc5_mk_term(tm, CVC5_KIND_APPLY_SELECTOR, 2, args2);

  printf("t2 is %s\n", cvc5_term_to_string(t2));
  printf("simplify(t2) is %s\n\n",
         cvc5_term_to_string(cvc5_simplify(slv, t2, false)));

  // You can also iterate over a Datatype to get all its constructors,
  // and over a DatatypeConstructor to get all its "args" (selectors)
  for (size_t i = 0, n = cvc5_dt_get_num_constructors(cons_list); i < n; ++i)
  {
    Cvc5DatatypeConstructor dtcons = cvc5_dt_get_constructor(cons_list, i);
    printf("ctor: %s\n", cvc5_dt_cons_to_string(dtcons));
    for (size_t j = 0, m = cvc5_dt_cons_get_num_selectors(dtcons); j < m; ++j)
    {
      Cvc5DatatypeSelector dtsel = cvc5_dt_cons_get_selector(dtcons, j);
      printf(" + arg: %s\n", cvc5_dt_sel_to_string(dtsel));
    }
  }
  printf("\n");

  // You can also define a tester term for constructor 'cons': (_ is cons)
  args2[0] = cvc5_dt_cons_get_tester_term(cons);
  args2[1] = t;
  Cvc5Term t_is_cons = cvc5_mk_term(tm, CVC5_KIND_APPLY_TESTER, 2, args2);
  printf("t_is_cons is %s\n\n", cvc5_term_to_string(t_is_cons));
  cvc5_assert_formula(slv, t_is_cons);
  // Updating t at 'head' with value 1 is defined as follows:
  args3[0] = cvc5_dt_sel_get_updater_term(head);
  args3[1] = t;
  args3[2] = cvc5_mk_integer_int64(tm, 1);
  Cvc5Term t_updated = cvc5_mk_term(tm, CVC5_KIND_APPLY_UPDATER, 3, args3);
  printf("t_updated is %s\n\n", cvc5_term_to_string(t_updated));
  args2[0] = t;
  args2[1] = t_updated;
  cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2));

  // You can also define parameterized datatypes.
  // This example builds a simple parameterized list of sort T, with one
  // constructor "cons".
  Cvc5Sort sort = cvc5_mk_param_sort(tm, "T");
  Cvc5Sort sorts[1] = {sort};
  Cvc5DatatypeDecl param_cons_list_decl =
      cvc5_mk_dt_decl_with_params(tm, "paramlist", 1, sorts, false);
  Cvc5DatatypeConstructorDecl param_cons = cvc5_mk_dt_cons_decl(tm, "cons");
  Cvc5DatatypeConstructorDecl param_nil = cvc5_mk_dt_cons_decl(tm, "nil");
  cvc5_dt_cons_decl_add_selector(param_cons, "head", sort);
  cvc5_dt_cons_decl_add_selector_self(param_cons, "tail");
  cvc5_dt_decl_add_constructor(param_cons_list_decl, param_cons);
  cvc5_dt_decl_add_constructor(param_cons_list_decl, param_nil);

  Cvc5Sort param_cons_list_sort = cvc5_mk_dt_sort(tm, param_cons_list_decl);
  sorts[0] = cvc5_get_integer_sort(tm);
  Cvc5Sort param_cons_int_list_sort =
      cvc5_sort_instantiate(param_cons_list_sort, 1, sorts);

  Cvc5Datatype param_cons_list = cvc5_sort_get_datatype(param_cons_list_sort);

  printf("parameterized datatype sort is\n");
  for (size_t i = 0, n = cvc5_dt_get_num_constructors(param_cons_list); i < n;
       ++i)
  {
    Cvc5DatatypeConstructor dtcons =
        cvc5_dt_get_constructor(param_cons_list, i);
    printf("ctor: %s\n", cvc5_dt_cons_to_string(dtcons));
    for (size_t j = 0, m = cvc5_dt_cons_get_num_selectors(dtcons); j < m; ++j)
    {
      Cvc5DatatypeSelector dtsel = cvc5_dt_cons_get_selector(dtcons, j);
      printf(" + arg: %s\n", cvc5_dt_sel_to_string(dtsel));
    }
  }

  Cvc5Term a = cvc5_mk_const(tm, param_cons_int_list_sort, "a");
  printf("term %s is of sort %s\n",
         cvc5_term_to_string(a),
         cvc5_sort_to_string(cvc5_term_get_sort(a)));

  args2[0] = cvc5_dt_sel_get_term(cvc5_dt_cons_get_selector_by_name(
      cvc5_dt_get_constructor_by_name(param_cons_list, "cons"), "head"));
  args2[1] = a;
  Cvc5Term head_a = cvc5_mk_term(tm, CVC5_KIND_APPLY_SELECTOR, 2, args2);

  printf("head_a is %s of sort %s\n",
         cvc5_term_to_string(head_a),
         cvc5_sort_to_string(cvc5_term_get_sort(head_a)));
  printf("sort of cons is %s\n\n",
         cvc5_sort_to_string(cvc5_term_get_sort(cvc5_dt_cons_get_term(
             cvc5_dt_get_constructor_by_name(param_cons_list, "cons")))));

  args2[0] = head_a;
  args2[1] = cvc5_mk_integer_int64(tm, 50);
  Cvc5Term assertion = cvc5_mk_term(tm, CVC5_KIND_GT, 2, args2);
  printf("Assert %s\n", cvc5_term_to_string(assertion));
  cvc5_assert_formula(slv, assertion);
  printf("Expect sat.\n");
  printf("cvc5: %s\n", cvc5_result_to_string(cvc5_check_sat(slv)));
}

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // This example builds a simple "cons list" of integers, with
  // two constructors, "cons" and "nil."

  // Building a datatype consists of two steps.
  // First, the datatype is specified.
  // Second, it is "resolved" to an actual sort, at which point function
  // symbols are assigned to its constructors, selectors, and testers.

  Cvc5DatatypeDecl cons_list_decl = cvc5_mk_dt_decl(tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(tm));
  cvc5_dt_cons_decl_add_selector_self(cons, "tail");
  cvc5_dt_decl_add_constructor(cons_list_decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(tm, "nil");
  cvc5_dt_decl_add_constructor(cons_list_decl, nil);

  printf("spec is:\n");
  printf("%s\n", cvc5_dt_decl_to_string(cons_list_decl));

  // Keep in mind that "DatatypeDecl" is the specification class for
  // datatypes---"DatatypeDecl" is not itself a cvc5 Sort.
  // Now that our Datatype is fully specified, we can get a Sort for it.
  // This step resolves the "SelfSort" reference and creates
  // symbols for all the constructors, etc.

  Cvc5Sort cons_list_sort = cvc5_mk_dt_sort(tm, cons_list_decl);

  test(tm, slv, cons_list_sort);

  printf("\n");
  printf(">>> Alternatively, use cvc5_declare_dt\n\n");

  Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons2, "head", cvc5_get_integer_sort(tm));
  cvc5_dt_cons_decl_add_selector_self(cons2, "tail");
  Cvc5DatatypeConstructorDecl nil2 = cvc5_mk_dt_cons_decl(tm, "nil");
  Cvc5DatatypeConstructorDecl ctors[2] = {cons2, nil2};
  Cvc5Sort cons_list_sort2 = cvc5_declare_dt(slv, "list2", 2, ctors);
  test(tm, slv, cons_list_sort2);

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
