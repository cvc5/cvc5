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
 * Black box testing of functions manipulating sorts of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackTermManager : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    // d_bool = cvc5_get_boolean_sort(d_tm);
    // d_int = cvc5_get_integer_sort(d_tm);
    // d_real = cvc5_get_real_sort(d_tm);
  }
  void TearDown() override { cvc5_term_manager_delete(d_tm); }

  Cvc5TermManager* d_tm;
  // Cvc5Sort d_bool;
  // Cvc5Sort d_int;
  // Cvc5Sort d_real;
};

TEST_F(TestCApiBlackTermManager, new) {}

TEST_F(TestCApiBlackTermManager, get_boolean_sort)
{
  (void)cvc5_get_boolean_sort(d_tm);
  ASSERT_DEATH(cvc5_get_boolean_sort(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, get_integer_sort)
{
  (void)cvc5_get_integer_sort(d_tm);
  ASSERT_DEATH(cvc5_get_integer_sort(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, get_real_sort)
{
  (void)cvc5_get_real_sort(d_tm);
  ASSERT_DEATH(cvc5_get_real_sort(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, get_regexp_sort)
{
  (void)cvc5_get_regexp_sort(d_tm);
  ASSERT_DEATH(cvc5_get_regexp_sort(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, get_string_sort)
{
  (void)cvc5_get_string_sort(d_tm);
  ASSERT_DEATH(cvc5_get_string_sort(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, get_rm_sort)
{
  (void)cvc5_get_rm_sort(d_tm);
  ASSERT_DEATH(cvc5_get_rm_sort(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_array_sort)
{
  Cvc5Sort bsort = cvc5_get_boolean_sort(d_tm);
  Cvc5Sort isort = cvc5_get_integer_sort(d_tm);
  Cvc5Sort rsort = cvc5_get_real_sort(d_tm);
  Cvc5Sort bvsort = cvc5_mk_bv_sort(d_tm, 32);
  (void)cvc5_mk_array_sort(d_tm, bsort, bsort);
  (void)cvc5_mk_array_sort(d_tm, isort, isort);
  (void)cvc5_mk_array_sort(d_tm, rsort, rsort);
  (void)cvc5_mk_array_sort(d_tm, bvsort, bvsort);
  (void)cvc5_mk_array_sort(d_tm, bsort, isort);
  (void)cvc5_mk_array_sort(d_tm, rsort, bvsort);

  Cvc5Sort fpsort = cvc5_mk_fp_sort(d_tm, 3, 5);
  (void)cvc5_mk_array_sort(d_tm, fpsort, fpsort);
  (void)cvc5_mk_array_sort(d_tm, bvsort, fpsort);

  ASSERT_DEATH(cvc5_mk_array_sort(nullptr, bvsort, fpsort),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_array_sort(d_tm, nullptr, fpsort), "invalid sort");
  ASSERT_DEATH(cvc5_mk_array_sort(d_tm, bvsort, nullptr), "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_array_sort(
      d_tm, cvc5_get_boolean_sort(tm), cvc5_get_integer_sort(tm));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_bv_sort)
{
  (void)cvc5_mk_bv_sort(d_tm, 32);
  ASSERT_DEATH(cvc5_mk_bv_sort(nullptr, 4), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_bv_sort(d_tm, 0), "expected size > 0");
}

TEST_F(TestCApiBlackTermManager, mk_ff_sort)
{
  (void)cvc5_mk_ff_sort(d_tm, "31", 10);
  ASSERT_DEATH(cvc5_mk_ff_sort(nullptr, "31", 10), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, nullptr, 10), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "6", 10), "expected modulus is prime");

  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "b", 10), "mpz_set_str");

  (void)cvc5_mk_ff_sort(d_tm, "1100101", 2);
  (void)cvc5_mk_ff_sort(d_tm, "10202", 3);
  (void)cvc5_mk_ff_sort(d_tm, "401", 5);
  (void)cvc5_mk_ff_sort(d_tm, "791a", 11);
  (void)cvc5_mk_ff_sort(d_tm, "970f", 16);
  (void)cvc5_mk_ff_sort(d_tm, "8CC5", 16);

  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "1100100", 2),
               "expected modulus is prime");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "10201", 3), "expected modulus is prime");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "400", 5), "expected modulus is prime");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "7919", 11), "expected modulus is prime");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "970e", 16), "expected modulus is prime");
  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "8CC4", 16), "expected modulus is prime");
}

TEST_F(TestCApiBlackTermManager, mk_fp_sort)
{
  (void)cvc5_mk_fp_sort(d_tm, 4, 8);
  ASSERT_DEATH(cvc5_mk_fp_sort(nullptr, 4, 8), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_fp_sort(d_tm, 0, 8), "expected exponent size > 1");
  ASSERT_DEATH(cvc5_mk_fp_sort(d_tm, 4, 0), "expected significand size > 1");
  ASSERT_DEATH(cvc5_mk_fp_sort(d_tm, 1, 8), "expected exponent size > 1");
  ASSERT_DEATH(cvc5_mk_fp_sort(d_tm, 4, 1), "expected significand size > 1");
}

TEST_F(TestCApiBlackTermManager, mk_dt_sort)
{
  {
    Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
    Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
    cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(d_tm));
    cvc5_dt_decl_add_constructor(decl, cons);
    Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
    cvc5_dt_decl_add_constructor(decl, nil);
    (void)cvc5_mk_dt_sort(d_tm, decl);
    ASSERT_DEATH(cvc5_mk_dt_sort(nullptr, decl), "unexpected NULL argument");
    ASSERT_DEATH(cvc5_mk_dt_sort(d_tm, decl), "is already resolved");
  }

  {
    Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
    ASSERT_DEATH(cvc5_mk_dt_sort(d_tm, decl), "at least one constructor");
  }

  {
    Cvc5TermManager* tm = cvc5_term_manager_new();
    ;
    Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(tm, "list", false);
    Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(tm, "cons");
    cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(tm));
    cvc5_dt_decl_add_constructor(decl, cons);
    Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(tm, "nil");
    cvc5_dt_decl_add_constructor(decl, nil);
    // this will throw when NodeManager is not a singleton anymore
    (void)cvc5_mk_dt_sort(d_tm, decl);
    cvc5_term_manager_delete(tm);
  }
}

TEST_F(TestCApiBlackTermManager, mk_dt_sorts)
{
  {
    Cvc5DatatypeDecl decl1 = cvc5_mk_dt_decl(d_tm, "list1", false);
    Cvc5DatatypeConstructorDecl cons1 = cvc5_mk_dt_cons_decl(d_tm, "cons1");
    cvc5_dt_cons_decl_add_selector(cons1, "head1", cvc5_get_integer_sort(d_tm));
    cvc5_dt_decl_add_constructor(decl1, cons1);
    Cvc5DatatypeConstructorDecl nil1 = cvc5_mk_dt_cons_decl(d_tm, "nil1");
    cvc5_dt_decl_add_constructor(decl1, nil1);
    Cvc5DatatypeDecl decl2 = cvc5_mk_dt_decl(d_tm, "list2", false);
    Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(d_tm, "cons2");
    cvc5_dt_cons_decl_add_selector(cons2, "head2", cvc5_get_integer_sort(d_tm));
    cvc5_dt_decl_add_constructor(decl2, cons2);
    Cvc5DatatypeConstructorDecl nil2 = cvc5_mk_dt_cons_decl(d_tm, "nil2");
    cvc5_dt_decl_add_constructor(decl2, nil2);
    std::vector<Cvc5DatatypeDecl> decls = {decl1, decl2};
    (void)cvc5_mk_dt_sorts(d_tm, decls.size(), decls.data());
    ASSERT_DEATH(cvc5_mk_dt_sorts(nullptr, decls.size(), decls.data()),
                 "unexpected NULL argument");
    ASSERT_DEATH(cvc5_mk_dt_sorts(d_tm, decls.size(), nullptr),
                 "unexpected NULL argument");

    ASSERT_DEATH(cvc5_mk_dt_sorts(d_tm, decls.size(), decls.data()),
                 "is already resolved");
  }

  {
    std::vector<Cvc5DatatypeDecl> decls = {
        cvc5_mk_dt_decl(d_tm, "list", "false")};
    ASSERT_DEATH(cvc5_mk_dt_sorts(d_tm, decls.size(), decls.data()),
                 "at least one constructor");
  }

  {
    /* with unresolved sorts */
    Cvc5Sort unresList = cvc5_mk_unresolved_dt_sort(d_tm, "ulist", 0);
    Cvc5DatatypeDecl ulist = cvc5_mk_dt_decl(d_tm, "ulist", false);
    Cvc5DatatypeConstructorDecl ucons = cvc5_mk_dt_cons_decl(d_tm, "ucons");
    cvc5_dt_cons_decl_add_selector(ucons, "car", unresList);
    cvc5_dt_cons_decl_add_selector(ucons, "cdr", unresList);
    cvc5_dt_decl_add_constructor(ulist, ucons);
    Cvc5DatatypeConstructorDecl unil = cvc5_mk_dt_cons_decl(d_tm, "unil");
    cvc5_dt_decl_add_constructor(ulist, unil);
    std::vector<Cvc5DatatypeDecl> udecls = {ulist};
    (void)cvc5_mk_dt_sorts(d_tm, udecls.size(), udecls.data());

    ASSERT_DEATH(cvc5_mk_dt_sorts(d_tm, udecls.size(), udecls.data()),
                 "has already been used");
  }

  {
    /* mutually recursive with unresolved parameterized sorts */
    Cvc5Sort p0 = cvc5_mk_param_sort(d_tm, "p0");
    Cvc5Sort p1 = cvc5_mk_param_sort(d_tm, "p1");
    Cvc5Sort u0 = cvc5_mk_unresolved_dt_sort(d_tm, "dt0", 1);
    Cvc5Sort u1 = cvc5_mk_unresolved_dt_sort(d_tm, "dt1", 1);
    std::vector<Cvc5Sort> sorts0 = {p0};
    std::vector<Cvc5Sort> sorts1 = {p1};
    Cvc5DatatypeDecl decl0 = cvc5_mk_dt_decl(d_tm, "dt0", sorts0.data());
    Cvc5DatatypeDecl decl1 = cvc5_mk_dt_decl(d_tm, "dt1", sorts1.data());
    Cvc5DatatypeConstructorDecl cons0 = cvc5_mk_dt_cons_decl(d_tm, "c0");
    cvc5_dt_cons_decl_add_selector(
        cons0, "s0", cvc5_sort_instantiate(u1, sorts0.size(), sorts0.data()));
    Cvc5DatatypeConstructorDecl cons1 = cvc5_mk_dt_cons_decl(d_tm, "c1");
    cvc5_dt_cons_decl_add_selector(
        cons1, "s1", cvc5_sort_instantiate(u0, sorts1.size(), sorts1.data()));
    cvc5_dt_decl_add_constructor(decl0, cons0);
    cvc5_dt_decl_add_constructor(decl1, cons1);
    cvc5_dt_decl_add_constructor(decl1, cvc5_mk_dt_cons_decl(d_tm, "nil"));
    std::vector<Cvc5DatatypeDecl> decls = {decl0, decl1};
    // const Cvc5Sort* dtsorts =
    //     cvc5_mk_dt_sorts(d_tm, decls.size(), decls.data());
    // std::vector<Cvc5Sort> iargs = {cvc5_get_boolean_sort(d_tm)};
    // Cvc5Sort isort =
    //     cvc5_sort_instantiate(dtsorts[1], iargs.size(), iargs.data());
    // Cvc5Term t1 = cvc5_mk_const(d_tm, isort, "t");
    // std::vector<Cvc5Term> children = {
    //     cvc5_dt_sel_get_term(cvc5_dt_get_selector(
    //         cvc5_sort_get_datatype(cvc5_term_get_sort(t1)), "s1")),
    //     t1};
    // Cvc5Term t0 = cvc5_mk_term(
    //     CVC5_KIND_APPLY_SELECTOR, children.size(), children.data());
    // iargs = {cvc5_get_boolean_sort(d_tm)};
    // ASSERT_EQ(cvc5_sort_instantiate(dtsorts[0], iargs.size(), iargs.data()),
    //           cvc5_term_get_sort(t0));
  }

  {
    Cvc5TermManager* tm = cvc5_term_manager_new();
    Cvc5DatatypeDecl decl1 = cvc5_mk_dt_decl(tm, "list1", false);
    Cvc5DatatypeConstructorDecl cons1 = cvc5_mk_dt_cons_decl(tm, "cons1");
    cvc5_dt_cons_decl_add_selector(cons1, "head1", cvc5_get_integer_sort(tm));
    cvc5_dt_decl_add_constructor(decl1, cons1);
    Cvc5DatatypeConstructorDecl nil1 = cvc5_mk_dt_cons_decl(tm, "nil1");
    cvc5_dt_decl_add_constructor(decl1, nil1);
    Cvc5DatatypeDecl decl2 = cvc5_mk_dt_decl(tm, "list2", false);
    Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(tm, "cons2");
    cvc5_dt_cons_decl_add_selector(cons2, "head2", cvc5_get_integer_sort(tm));
    cvc5_dt_decl_add_constructor(decl2, cons2);
    Cvc5DatatypeConstructorDecl nil2 = cvc5_mk_dt_cons_decl(tm, "nil2");
    cvc5_dt_decl_add_constructor(decl2, nil2);
    std::vector<Cvc5DatatypeDecl> decls = {decl1, decl2};
    // this will throw when NodeManager is not a singleton anymore
    (void)cvc5_mk_dt_sorts(d_tm, decls.size(), decls.data());
    cvc5_term_manager_delete(tm);
  }
}

TEST_F(TestCApiBlackTermManager, mk_fun_sort)
{
  Cvc5Sort unsort = cvc5_mk_uninterpreted_sort(d_tm, "u");
  std::vector<Cvc5Sort> domain = {unsort};
  Cvc5Sort intsort = cvc5_get_integer_sort(d_tm);
  Cvc5Sort funsort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);

  // function arguments are allowed
  domain = {funsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);
  ASSERT_DEATH(cvc5_mk_fun_sort(nullptr, domain.size(), domain.data(), intsort),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), nullptr, intsort),
               "unexpected NULL argument");
  domain = {nullptr};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort),
               "invalid sort at index 0");
  // non-first-class arguments are not allowed
  Cvc5Sort regexpsort = cvc5_get_regexp_sort(d_tm);
  domain = {regexpsort};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort),
               "expected first-class sort as domain sort");
  domain = {intsort};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), funsort),
               "expected non-function sort as codomain sort");

  domain = {unsort, intsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);

  domain = {unsort};
  funsort = cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);

  // function arguments are allowed
  domain = {funsort, unsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);

  domain = {intsort, unsort};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), funsort),
               "expected non-function sort as codomain sort");

  domain = {cvc5_get_boolean_sort(d_tm), intsort, intsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);
  domain = {cvc5_get_boolean_sort(d_tm), intsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), intsort);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_fun_sort(
      tm, domain.size(), domain.data(), cvc5_get_integer_sort(tm));
  domain = {cvc5_get_boolean_sort(tm), cvc5_get_integer_sort(tm)};
  (void)cvc5_mk_fun_sort(tm, domain.size(), domain.data(), intsort);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_param_sort)
{
  (void)cvc5_mk_param_sort(d_tm, "T");
  (void)cvc5_mk_param_sort(d_tm, "");
  ASSERT_DEATH(cvc5_mk_param_sort(nullptr, ""), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_param_sort(d_tm, nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_predicate_sort)
{
  Cvc5Sort intsort = cvc5_get_integer_sort(d_tm);
  std::vector<Cvc5Sort> sorts = {intsort};
  (void)cvc5_mk_predicate_sort(d_tm, sorts.size(), sorts.data());
  ASSERT_DEATH(cvc5_mk_predicate_sort(nullptr, sorts.size(), sorts.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_predicate_sort(d_tm, sorts.size(), nullptr),
               "unexpected NULL argument");
  sorts = {nullptr};
  ASSERT_DEATH(cvc5_mk_predicate_sort(d_tm, sorts.size(), sorts.data()),
               "invalid sort at index 0");

  sorts = {};
  ASSERT_DEATH(cvc5_mk_predicate_sort(d_tm, sorts.size(), sorts.data()),
               "expected at least one parameter sort");

  sorts = {nullptr};
  ASSERT_DEATH(cvc5_mk_predicate_sort(d_tm, sorts.size(), sorts.data()),
               "invalid sort at index 0");

  sorts = {cvc5_mk_uninterpreted_sort(d_tm, "u"), intsort};
  Cvc5Sort funsort =
      cvc5_mk_fun_sort(d_tm, sorts.size(), sorts.data(), intsort);
  // functions as arguments are allowed
  sorts = {funsort, intsort};
  (void)cvc5_mk_predicate_sort(d_tm, sorts.size(), sorts.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  sorts = {intsort};
  (void)cvc5_mk_predicate_sort(tm, sorts.size(), sorts.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_record_sort)
{
  std::vector<const char*> names = {};
  std::vector<Cvc5Sort> sorts = {};
  (void)cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data());
  ASSERT_DEATH(
      cvc5_mk_record_sort(nullptr, names.size(), names.data(), sorts.data()),
      "unexpected NULL argument");

  names = {"b", nullptr, "i"};
  ASSERT_DEATH(
      cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data()),
      "unexpected NULL argument");

  names = {"b", "bv", "i"};

  sorts = {nullptr, cvc5_mk_bv_sort(d_tm, 8), cvc5_get_integer_sort(d_tm)};
  ASSERT_DEATH(
      cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data()),
      "invalid sort at index 0");

  sorts = {cvc5_get_boolean_sort(d_tm),
           cvc5_mk_bv_sort(d_tm, 8),
           cvc5_get_integer_sort(d_tm)};
  // Cvc5Sort recsort =
  cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data());

  //(void)cvc5_sort_get_datatype(recsort);
  (void)cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  sorts = {cvc5_get_boolean_sort(tm),
           cvc5_mk_bv_sort(d_tm, 8),
           cvc5_get_integer_sort(tm)};
  (void)cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_set_sort)
{
  (void)cvc5_mk_set_sort(d_tm, cvc5_get_boolean_sort(d_tm));
  (void)cvc5_mk_set_sort(d_tm, cvc5_get_integer_sort(d_tm));
  (void)cvc5_mk_set_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  (void)cvc5_mk_set_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  ASSERT_DEATH(cvc5_mk_set_sort(nullptr, cvc5_get_boolean_sort(d_tm)),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_set_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_set_sort(d_tm, cvc5_get_boolean_sort(tm));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_bag_sort)
{
  (void)cvc5_mk_bag_sort(d_tm, cvc5_get_boolean_sort(d_tm));
  (void)cvc5_mk_bag_sort(d_tm, cvc5_get_integer_sort(d_tm));
  (void)cvc5_mk_bag_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  (void)cvc5_mk_bag_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  ASSERT_DEATH(cvc5_mk_bag_sort(nullptr, cvc5_get_boolean_sort(d_tm)),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_bag_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_bag_sort(d_tm, cvc5_get_boolean_sort(tm));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_sequence_sort)
{
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_get_boolean_sort(d_tm));
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_get_integer_sort(d_tm));
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  ASSERT_DEATH(cvc5_mk_sequence_sort(nullptr, cvc5_get_boolean_sort(d_tm)),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_sequence_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_get_boolean_sort(tm));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_abstract_sort)
{
  (void)cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_ARRAY_SORT);
  (void)cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_BITVECTOR_SORT);
  (void)cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_TUPLE_SORT);
  (void)cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_SET_SORT);
  ASSERT_DEATH(cvc5_mk_abstract_sort(nullptr, CVC5_SORT_KIND_SET_SORT),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_BOOLEAN_SORT),
               "Cannot construct abstract type");
  ASSERT_DEATH(cvc5_mk_abstract_sort(d_tm, static_cast<Cvc5SortKind>(-1)),
               "Cannot construct abstract type");
}

TEST_F(TestCApiBlackTermManager, mk_uninterpreted_sort)
{
  (void)cvc5_mk_uninterpreted_sort(d_tm, "u");
  (void)cvc5_mk_uninterpreted_sort(d_tm, "");
  ASSERT_DEATH(cvc5_mk_uninterpreted_sort(nullptr, ""),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_unresolved_dt_sort)
{
  (void)cvc5_mk_unresolved_dt_sort(d_tm, "u", 0);
  (void)cvc5_mk_unresolved_dt_sort(d_tm, "u", 1);
  (void)cvc5_mk_unresolved_dt_sort(d_tm, "", 0);
  (void)cvc5_mk_unresolved_dt_sort(d_tm, "", 1);
  ASSERT_DEATH(cvc5_mk_unresolved_dt_sort(nullptr, "", 1),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_unresolved_dt_sort(d_tm, nullptr, 1),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_uninterpreted_sort_constructor_sort)
{
  (void)cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, "s");
  (void)cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, "");
  (void)cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, nullptr);
  ASSERT_DEATH(cvc5_mk_uninterpreted_sort_constructor_sort(nullptr, 2, "s"),
               "unexpected NULL argument");
  (void)cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, nullptr);
  ASSERT_DEATH(cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 0, ""),
               "expected an arity > 0");
}

TEST_F(TestCApiBlackTermManager, mk_tuple_sort)
{
  Cvc5Sort intsort = cvc5_get_integer_sort(d_tm);
  std::vector<Cvc5Sort> sorts = {intsort};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  ASSERT_DEATH(cvc5_mk_tuple_sort(nullptr, sorts.size(), sorts.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_tuple_sort(nullptr, sorts.size(), nullptr),
               "unexpected NULL argument");
  sorts = {intsort, nullptr};
  ASSERT_DEATH(cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data()),
               "invalid sort at index 1");
  sorts = {cvc5_mk_uninterpreted_sort(d_tm, "u"), intsort};
  Cvc5Sort funsort = cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  sorts = {intsort, funsort};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  sorts = {intsort};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  sorts = {cvc5_get_boolean_sort(tm)};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_sort)
{
  Cvc5Sort intsort = cvc5_get_integer_sort(d_tm);
  (void)cvc5_mk_nullable_sort(d_tm, intsort);
  (void)cvc5_mk_nullable_sort(d_tm, intsort);
  ASSERT_DEATH(cvc5_mk_nullable_sort(nullptr, intsort),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_nullable_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_sort(tm, intsort);
  cvc5_term_manager_delete(tm);
}

}  // namespace cvc5::internal::test
