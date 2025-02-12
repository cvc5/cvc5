/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include <cmath>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackTermManager : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_int = cvc5_get_integer_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
  }
  void TearDown() override { cvc5_term_manager_delete(d_tm); }

  Cvc5TermManager* d_tm;
  Cvc5Sort d_bool;
  Cvc5Sort d_int;
  Cvc5Sort d_real;
};

TEST_F(TestCApiBlackTermManager, new) {}

TEST_F(TestCApiBlackTermManager, delete)
{
  ASSERT_DEATH(cvc5_term_manager_delete(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, release)
{
  ASSERT_DEATH(cvc5_term_manager_release(nullptr), "unexpected NULL argument");
  cvc5_term_manager_release(d_tm);
}

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
  Cvc5Sort bvsort = cvc5_mk_bv_sort(d_tm, 32);
  (void)cvc5_mk_array_sort(d_tm, d_bool, d_bool);
  (void)cvc5_mk_array_sort(d_tm, d_int, d_int);
  (void)cvc5_mk_array_sort(d_tm, d_real, d_real);
  (void)cvc5_mk_array_sort(d_tm, bvsort, bvsort);
  (void)cvc5_mk_array_sort(d_tm, d_bool, d_int);
  (void)cvc5_mk_array_sort(d_tm, d_real, bvsort);

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

  ASSERT_DEATH(cvc5_mk_ff_sort(d_tm, "b", 10), "");

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
    cvc5_dt_cons_decl_add_selector(cons, "head", d_int);
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
    cvc5_dt_cons_decl_add_selector(cons1, "head1", d_int);
    cvc5_dt_decl_add_constructor(decl1, cons1);
    Cvc5DatatypeConstructorDecl nil1 = cvc5_mk_dt_cons_decl(d_tm, "nil1");
    cvc5_dt_decl_add_constructor(decl1, nil1);
    Cvc5DatatypeDecl decl2 = cvc5_mk_dt_decl(d_tm, "list2", false);
    Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(d_tm, "cons2");
    cvc5_dt_cons_decl_add_selector(cons2, "head2", d_int);
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
    Cvc5DatatypeDecl decl0 =
        cvc5_mk_dt_decl_with_params(d_tm, "dt0", 1, sorts0.data(), false);
    Cvc5DatatypeDecl decl1 =
        cvc5_mk_dt_decl_with_params(d_tm, "dt1", 1, sorts1.data(), false);
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
    const Cvc5Sort* dtsorts =
        cvc5_mk_dt_sorts(d_tm, decls.size(), decls.data());

    std::vector<Cvc5Sort> iargs = {cvc5_get_boolean_sort(d_tm)};
    Cvc5Sort isort =
        cvc5_sort_instantiate(dtsorts[1], iargs.size(), iargs.data());
    Cvc5Term t1 = cvc5_mk_const(d_tm, isort, "t");
    std::vector<Cvc5Term> children = {
        cvc5_dt_sel_get_term(cvc5_dt_get_selector(
            cvc5_sort_get_datatype(cvc5_term_get_sort(t1)), "s1")),
        t1};
    Cvc5Term t0 = cvc5_mk_term(
        d_tm, CVC5_KIND_APPLY_SELECTOR, children.size(), children.data());
    iargs = {cvc5_get_boolean_sort(d_tm)};
    ASSERT_EQ(cvc5_sort_instantiate(dtsorts[0], iargs.size(), iargs.data()),
              cvc5_term_get_sort(t0));
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
  Cvc5Sort funsort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  // function arguments are allowed
  domain = {funsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  ASSERT_DEATH(cvc5_mk_fun_sort(nullptr, domain.size(), domain.data(), d_int),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), nullptr, d_int),
               "unexpected NULL argument");
  domain = {nullptr};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int),
               "invalid sort at index 0");
  // non-first-class arguments are not allowed
  Cvc5Sort regexpsort = cvc5_get_regexp_sort(d_tm);
  domain = {regexpsort};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int),
               "expected first-class sort as domain sort");
  domain = {d_int};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), funsort),
               "expected non-function sort as codomain sort");

  domain = {unsort, d_int};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  domain = {unsort};
  funsort = cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  // function arguments are allowed
  domain = {funsort, unsort};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  domain = {d_int, unsort};
  ASSERT_DEATH(cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), funsort),
               "expected non-function sort as codomain sort");

  domain = {d_bool, d_int, d_int};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_bool, d_int};
  (void)cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_fun_sort(
      tm, domain.size(), domain.data(), cvc5_get_integer_sort(tm));
  domain = {cvc5_get_boolean_sort(tm), cvc5_get_integer_sort(tm)};
  (void)cvc5_mk_fun_sort(tm, domain.size(), domain.data(), d_int);
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
  std::vector<Cvc5Sort> sorts = {d_int};
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

  sorts = {cvc5_mk_uninterpreted_sort(d_tm, "u"), d_int};
  Cvc5Sort funsort = cvc5_mk_fun_sort(d_tm, sorts.size(), sorts.data(), d_int);
  // functions as arguments are allowed
  sorts = {funsort, d_int};
  (void)cvc5_mk_predicate_sort(d_tm, sorts.size(), sorts.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  sorts = {d_int};
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

  sorts = {nullptr, cvc5_mk_bv_sort(d_tm, 8), d_int};
  ASSERT_DEATH(
      cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data()),
      "invalid sort at index 0");

  sorts = {d_bool, cvc5_mk_bv_sort(d_tm, 8), d_int};
  Cvc5Sort recsort =
      cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data());
  (void)cvc5_sort_get_datatype(recsort);
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
  (void)cvc5_mk_set_sort(d_tm, d_bool);
  (void)cvc5_mk_set_sort(d_tm, d_int);
  (void)cvc5_mk_set_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  (void)cvc5_mk_set_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  ASSERT_DEATH(cvc5_mk_set_sort(nullptr, d_bool), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_set_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_set_sort(d_tm, cvc5_get_boolean_sort(tm));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_bag_sort)
{
  (void)cvc5_mk_bag_sort(d_tm, d_bool);
  (void)cvc5_mk_bag_sort(d_tm, d_int);
  (void)cvc5_mk_bag_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  (void)cvc5_mk_bag_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  ASSERT_DEATH(cvc5_mk_bag_sort(nullptr, d_bool), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_bag_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_bag_sort(d_tm, cvc5_get_boolean_sort(tm));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_sequence_sort)
{
  (void)cvc5_mk_sequence_sort(d_tm, d_bool);
  (void)cvc5_mk_sequence_sort(d_tm, d_int);
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  (void)cvc5_mk_sequence_sort(d_tm, cvc5_mk_bv_sort(d_tm, 4));
  ASSERT_DEATH(cvc5_mk_sequence_sort(nullptr, d_bool),
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
               "cannot construct abstract type");
  ASSERT_DEATH(cvc5_mk_abstract_sort(d_tm, static_cast<Cvc5SortKind>(-1)),
               "cannot construct abstract type");
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
  std::vector<Cvc5Sort> sorts = {d_int};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  ASSERT_DEATH(cvc5_mk_tuple_sort(nullptr, sorts.size(), sorts.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_tuple_sort(nullptr, sorts.size(), nullptr),
               "unexpected NULL argument");
  sorts = {d_int, nullptr};
  ASSERT_DEATH(cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data()),
               "invalid sort at index 1");
  sorts = {cvc5_mk_uninterpreted_sort(d_tm, "u"), d_int};
  Cvc5Sort funsort = cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  sorts = {d_int, funsort};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  sorts = {d_int};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  sorts = {cvc5_get_boolean_sort(tm)};
  (void)cvc5_mk_tuple_sort(d_tm, sorts.size(), sorts.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_sort)
{
  (void)cvc5_mk_nullable_sort(d_tm, d_int);
  (void)cvc5_mk_nullable_sort(d_tm, d_int);

  ASSERT_DEATH(cvc5_mk_nullable_sort(nullptr, d_int),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_nullable_sort(d_tm, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_sort(tm, d_int);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_bv)
{
  (void)cvc5_mk_bv(d_tm, 8, "-1111111", 2);
  (void)cvc5_mk_bv(d_tm, 8, "0101", 2);
  (void)cvc5_mk_bv(d_tm, 8, "00000101", 2);
  (void)cvc5_mk_bv(d_tm, 8, "-127", 10);
  (void)cvc5_mk_bv(d_tm, 8, "255", 10);
  (void)cvc5_mk_bv(d_tm, 8, "-7f", 16);
  (void)cvc5_mk_bv(d_tm, 8, "a0", 16);

  ASSERT_DEATH(cvc5_mk_bv(nullptr, 8, "-1111111", 2),
               "unexpected NULL argument");

  ASSERT_DEATH(cvc5_mk_bv(d_tm, 0, "-127", 10),
               "invalid argument '0' for 'size'");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 0, "a0", 16),
               "invalid argument '0' for 'size'");

  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "", 2), "expected a non-empty string");

  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "101", 5), "expected base 2, 10, or 16");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "128", 11), "expected base 2, 10, or 16");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "a0", 21), "expected base 2, 10, or 16");

  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "-11111111", 2),
               "overflow in bit-vector construction");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "101010101", 2),
               "overflow in bit-vector construction");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "-256", 10),
               "overflow in bit-vector construction");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "257", 10),
               "overflow in bit-vector construction");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "-a0", 16),
               "overflow in bit-vector construction");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "fffff", 16),
               "overflow in bit-vector construction");

  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "10201010", 2), "");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "-25x", 10), "");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "2x7", 10), "");
  ASSERT_DEATH(cvc5_mk_bv(d_tm, 8, "fzff", 16), "");

  ASSERT_EQ(cvc5_mk_bv(d_tm, 8, "0101", 2), cvc5_mk_bv(d_tm, 8, "00000101", 2));
  ASSERT_EQ(cvc5_mk_bv(d_tm, 4, "-1", 2), cvc5_mk_bv(d_tm, 4, "1111", 2));
  ASSERT_EQ(cvc5_mk_bv(d_tm, 4, "-1", 16), cvc5_mk_bv(d_tm, 4, "1111", 2));
  ASSERT_EQ(cvc5_mk_bv(d_tm, 4, "-1", 10), cvc5_mk_bv(d_tm, 4, "1111", 2));
  ASSERT_EQ(cvc5_term_to_string(cvc5_mk_bv(d_tm, 8, "01010101", 2)),
            std::string("#b01010101"));
  ASSERT_EQ(cvc5_term_to_string(cvc5_mk_bv(d_tm, 8, "F", 16)),
            std::string("#b00001111"));
  ASSERT_EQ(cvc5_mk_bv(d_tm, 8, "-1", 10), cvc5_mk_bv(d_tm, 8, "FF", 16));
}

TEST_F(TestCApiBlackTermManager, mk_bv_uint64)
{
  (void)cvc5_mk_bv_uint64(d_tm, 8, 2);
  (void)cvc5_mk_bv_uint64(d_tm, 32, 2);
  ASSERT_DEATH(cvc5_mk_bv_uint64(nullptr, 0, 2), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_bv_uint64(d_tm, 0, 2),
               "invalid argument '0' for 'size'");
}

TEST_F(TestCApiBlackTermManager, mk_ff_elem)
{
  Cvc5Sort ff_sort = cvc5_mk_ff_sort(d_tm, "7", 10);
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 4);

  (void)cvc5_mk_ff_elem(d_tm, "0", ff_sort, 10);
  (void)cvc5_mk_ff_elem(d_tm, "1", ff_sort, 10);
  (void)cvc5_mk_ff_elem(d_tm, "6", ff_sort, 10);
  (void)cvc5_mk_ff_elem(d_tm, "8", ff_sort, 10);
  (void)cvc5_mk_ff_elem(d_tm, "-1", ff_sort, 10);

  ASSERT_DEATH(cvc5_mk_ff_elem(nullptr, "-1", ff_sort, 10),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_ff_elem(d_tm, "a", ff_sort, 10), "");
  ASSERT_DEATH(cvc5_mk_ff_elem(d_tm, "-1", bv_sort, 10),
               "expected a finite field sort");

  ASSERT_EQ(cvc5_mk_ff_elem(d_tm, "-1", ff_sort, 10),
            cvc5_mk_ff_elem(d_tm, "6", ff_sort, 10));
  ASSERT_EQ(cvc5_mk_ff_elem(d_tm, "1", ff_sort, 10),
            cvc5_mk_ff_elem(d_tm, "8", ff_sort, 10));

  (void)cvc5_mk_ff_elem(d_tm, "0", ff_sort, 2);
  (void)cvc5_mk_ff_elem(d_tm, "101", ff_sort, 3);
  (void)cvc5_mk_ff_elem(d_tm, "-10", ff_sort, 7);
  (void)cvc5_mk_ff_elem(d_tm, "abcde", ff_sort, 16);

  ASSERT_EQ(cvc5_mk_ff_elem(d_tm, "0", ff_sort, 2),
            cvc5_mk_ff_elem(d_tm, "0", ff_sort, 3));
  ASSERT_EQ(cvc5_mk_ff_elem(d_tm, "11", ff_sort, 2),
            cvc5_mk_ff_elem(d_tm, "10", ff_sort, 3));
  ASSERT_EQ(cvc5_mk_ff_elem(d_tm, "1010", ff_sort, 2),
            cvc5_mk_ff_elem(d_tm, "A", ff_sort, 16));

  ASSERT_EQ(cvc5_mk_ff_elem(d_tm, "-22", ff_sort, 3),
            cvc5_mk_ff_elem(d_tm, "10", ff_sort, 6));
}

TEST_F(TestCApiBlackTermManager, mk_const_array)
{
  Cvc5Sort arr_sort = cvc5_mk_array_sort(d_tm, d_int, d_int);
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  (void)cvc5_mk_const_array(d_tm, arr_sort, zero);

  ASSERT_DEATH(cvc5_mk_const_array(nullptr, arr_sort, zero),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, nullptr, zero), "invalid sort");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, arr_sort, nullptr), "invalid term");
  ASSERT_DEATH(
      cvc5_mk_const_array(d_tm, arr_sort, cvc5_mk_bv_uint64(d_tm, 1, 1)),
      "value does not match element sort");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, d_int, zero),
               "expected an array sort");

  Cvc5Sort arr_sort2 = cvc5_mk_array_sort(d_tm, d_int, d_int);
  Cvc5Term zero2 = cvc5_mk_integer_int64(d_tm, 0);
  (void)cvc5_mk_const_array(d_tm, arr_sort2, zero);
  (void)cvc5_mk_const_array(d_tm, arr_sort, zero2);
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_const_array(tm, arr_sort, cvc5_mk_integer_int64(tm, 0));
  (void)cvc5_mk_const_array(
      tm,
      cvc5_mk_array_sort(
          tm, cvc5_get_integer_sort(tm), cvc5_get_integer_sort(tm)),
      zero);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_var)
{
  std::vector<Cvc5Sort> domain = {d_int};
  Cvc5Sort fun_sort = cvc5_mk_fun_sort(d_tm, 1, domain.data(), d_bool);

  (void)cvc5_mk_var(d_tm, d_bool, nullptr);
  (void)cvc5_mk_var(d_tm, fun_sort, nullptr);
  (void)cvc5_mk_var(d_tm, d_bool, "b");
  (void)cvc5_mk_var(d_tm, fun_sort, "");

  ASSERT_DEATH(cvc5_mk_var(nullptr, d_bool, ""), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_var(d_tm, nullptr, ""), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_var(tm, d_bool, "b");
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_boolean)
{
  (void)cvc5_mk_boolean(d_tm, true);
  (void)cvc5_mk_boolean(d_tm, false);
  ASSERT_DEATH(cvc5_mk_boolean(nullptr, true), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_rm)
{
  ASSERT_EQ(
      cvc5_term_to_string(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN)),
      std::string("roundNearestTiesToEven"));
  ASSERT_EQ(
      cvc5_term_to_string(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_TOWARD_POSITIVE)),
      std::string("roundTowardPositive"));
  ASSERT_EQ(
      cvc5_term_to_string(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_TOWARD_NEGATIVE)),
      std::string("roundTowardNegative"));
  ASSERT_EQ(cvc5_term_to_string(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_TOWARD_ZERO)),
            std::string("roundTowardZero"));
  ASSERT_EQ(
      cvc5_term_to_string(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_NEAREST_TIES_TO_AWAY)),
      std::string("roundNearestTiesToAway"));
  ASSERT_DEATH(cvc5_mk_rm(nullptr, CVC5_RM_ROUND_TOWARD_ZERO),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_fp)
{
  Cvc5Term t1 = cvc5_mk_bv_uint64(d_tm, 8, 0);
  Cvc5Term t2 = cvc5_mk_bv_uint64(d_tm, 4, 0);

  (void)cvc5_mk_fp(d_tm, 3, 5, t1);
  ASSERT_DEATH(cvc5_mk_fp(nullptr, 3, 5, t1), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_fp(d_tm, 3, 5, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_mk_fp(d_tm, 0, 5, t1), "expected exponent size > 1");
  ASSERT_DEATH(cvc5_mk_fp(d_tm, 1, 5, t1), "expected exponent size > 1");
  ASSERT_DEATH(cvc5_mk_fp(d_tm, 3, 0, t1), "expected significand size > 1");
  ASSERT_DEATH(cvc5_mk_fp(d_tm, 3, 1, t1), "expected significand size > 1");
  ASSERT_DEATH(cvc5_mk_fp(d_tm, 3, 5, t2),
               "expected a bit-vector value with bit-width '8'");

  Cvc5Term sign = cvc5_mk_bv_uint64(d_tm, 1, 0);
  Cvc5Term exp = cvc5_mk_bv_uint64(d_tm, 5, 0);
  Cvc5Term sig = cvc5_mk_bv_uint64(d_tm, 10, 0);
  ASSERT_EQ(cvc5_mk_fp_from_ieee(d_tm, sign, exp, sig),
            cvc5_mk_fp(d_tm, 5, 11, cvc5_mk_bv_uint64(d_tm, 16, 0)));

  ASSERT_DEATH(cvc5_mk_fp_from_ieee(nullptr, sign, exp, sig),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_fp_from_ieee(d_tm, nullptr, exp, sig), "invalid term");
  ASSERT_DEATH(cvc5_mk_fp_from_ieee(d_tm, sign, nullptr, sig), "invalid term");
  ASSERT_DEATH(cvc5_mk_fp_from_ieee(d_tm, sign, exp, nullptr), "invalid term");
  ASSERT_DEATH(
      cvc5_mk_fp_from_ieee(
          d_tm, cvc5_mk_const(d_tm, cvc5_mk_bv_sort(d_tm, 1), ""), exp, sig),
      "expected bit-vector value");
  ASSERT_DEATH(
      cvc5_mk_fp_from_ieee(
          d_tm, sign, cvc5_mk_const(d_tm, cvc5_mk_bv_sort(d_tm, 5), ""), sig),
      "expected bit-vector value");
  ASSERT_DEATH(
      cvc5_mk_fp_from_ieee(
          d_tm, sign, exp, cvc5_mk_const(d_tm, cvc5_mk_bv_sort(d_tm, 10), "")),
      "expected bit-vector value");
  ASSERT_DEATH(
      cvc5_mk_fp_from_ieee(d_tm, cvc5_mk_bv_uint64(d_tm, 2, 0), exp, sig),
      "expected a bit-vector value of size 1");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_fp(tm, 3, 5, t1);
  (void)cvc5_mk_fp_from_ieee(
      tm, sign, cvc5_mk_bv_uint64(tm, 5, 0), cvc5_mk_bv_uint64(tm, 10, 0));
  (void)cvc5_mk_fp_from_ieee(
      tm, cvc5_mk_bv_uint64(tm, 1, 0), exp, cvc5_mk_bv_uint64(tm, 10, 0));
  (void)cvc5_mk_fp_from_ieee(
      tm, cvc5_mk_bv_uint64(tm, 1, 0), cvc5_mk_bv_uint64(tm, 5, 0), sig);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_cardinality_constraint)
{
  Cvc5Sort unsort = cvc5_mk_uninterpreted_sort(d_tm, "u");
  (void)cvc5_mk_cardinality_constraint(d_tm, unsort, 3);
  ASSERT_DEATH(cvc5_mk_cardinality_constraint(nullptr, unsort, 3),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_cardinality_constraint(d_tm, nullptr, 3),
               "invalid sort");
  ASSERT_DEATH(cvc5_mk_cardinality_constraint(d_tm, d_int, 3),
               "expected an uninterpreted sort");
  ASSERT_DEATH(cvc5_mk_cardinality_constraint(d_tm, unsort, 0),
               "expected a value > 0");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_cardinality_constraint(tm, unsort, 3);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_empty_set)
{
  Cvc5Sort sort = cvc5_mk_set_sort(d_tm, d_bool);
  (void)cvc5_mk_empty_set(d_tm, sort);
  ASSERT_DEATH(cvc5_mk_empty_set(nullptr, sort), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_empty_set(d_tm, nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_mk_empty_set(d_tm, d_bool),
               "expected null sort or set sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_empty_set(tm, sort);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_empty_bag)
{
  Cvc5Sort sort = cvc5_mk_bag_sort(d_tm, d_bool);
  (void)cvc5_mk_empty_bag(d_tm, sort);
  ASSERT_DEATH(cvc5_mk_empty_bag(nullptr, sort), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_empty_bag(d_tm, nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_mk_empty_bag(d_tm, d_bool),
               "expected null sort or bag sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_empty_bag(tm, sort);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_empty_sequence)
{
  Cvc5Sort sort = cvc5_mk_sequence_sort(d_tm, d_bool);
  (void)cvc5_mk_empty_sequence(d_tm, sort);
  (void)cvc5_mk_empty_sequence(d_tm, d_bool);
  ASSERT_DEATH(cvc5_mk_empty_sequence(nullptr, sort),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_empty_sequence(d_tm, nullptr), "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_empty_sequence(tm, sort);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_false) { (void)cvc5_mk_false(d_tm); }

TEST_F(TestCApiBlackTermManager, mk_fp_nan)
{
  (void)cvc5_mk_fp_nan(d_tm, 3, 5);
  ASSERT_DEATH(cvc5_mk_fp_nan(nullptr, 3, 5), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_fp_neg_zero)
{
  (void)cvc5_mk_fp_neg_zero(d_tm, 3, 5);
  ASSERT_DEATH(cvc5_mk_fp_neg_zero(nullptr, 3, 5), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_fp_pos_zero)
{
  (void)cvc5_mk_fp_pos_zero(d_tm, 3, 5);
  ASSERT_DEATH(cvc5_mk_fp_pos_zero(nullptr, 3, 5), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_fp_neg_inf)
{
  (void)cvc5_mk_fp_neg_inf(d_tm, 3, 5);
  ASSERT_DEATH(cvc5_mk_fp_neg_inf(nullptr, 3, 5), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_fp_pos_inf)
{
  (void)cvc5_mk_fp_pos_inf(d_tm, 3, 5);
  ASSERT_DEATH(cvc5_mk_fp_pos_inf(nullptr, 3, 5), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_op)
{
  (void)cvc5_mk_op_from_str(d_tm, CVC5_KIND_DIVISIBLE, "2147483648");
  ASSERT_DEATH(cvc5_mk_op_from_str(nullptr, CVC5_KIND_DIVISIBLE, "2147483648"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_op_from_str(d_tm, CVC5_KIND_DIVISIBLE, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_op_from_str(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, "1"),
               "expected DIVISIBLE");

  std::vector<uint32_t> idxs = {1};
  (void)cvc5_mk_op(d_tm, CVC5_KIND_DIVISIBLE, 1, idxs.data());
  (void)cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_ROTATE_LEFT, 1, idxs.data());
  (void)cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_ROTATE_RIGHT, 1, idxs.data());
  ASSERT_DEATH(
      cvc5_mk_op(nullptr, CVC5_KIND_BITVECTOR_ROTATE_RIGHT, 1, idxs.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_ROTATE_RIGHT, 1, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, 1, idxs.data()),
               "expected 2 but got 1");

  idxs = {1, 1};
  (void)cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs.data());
  ASSERT_DEATH(cvc5_mk_op(d_tm, CVC5_KIND_DIVISIBLE, 2, idxs.data()),
               "expected 1 but got 2");

  idxs = {1, 2, 2};
  (void)cvc5_mk_op(d_tm, CVC5_KIND_TUPLE_PROJECT, 3, idxs.data());
}

TEST_F(TestCApiBlackTermManager, mk_pi)
{
  (void)(cvc5_mk_pi(d_tm));
  ASSERT_DEATH(cvc5_mk_pi(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_integer)
{
  (void)cvc5_mk_integer(d_tm, "123");
  ASSERT_DEATH(cvc5_mk_integer(nullptr, "123"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, nullptr), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "1.23"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "1/23"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "12/3"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, ".2"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "2."), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, ""), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "asdf"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "1.2/3"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "."), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "/"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "2/"), "expected an integer");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "/2"), "expected an integer");

  (void)cvc5_mk_integer_int64(d_tm, 1);
  (void)cvc5_mk_integer_int64(d_tm, -1);
}

TEST_F(TestCApiBlackTermManager, mkReal)
{
  (void)cvc5_mk_real(d_tm, "123");
  (void)cvc5_mk_real(d_tm, "1.23");
  (void)cvc5_mk_real(d_tm, "1/23");
  (void)cvc5_mk_real(d_tm, "12/3");
  (void)cvc5_mk_real(d_tm, "2.");
  (void)cvc5_mk_real(d_tm, ".2");
  (void)cvc5_mk_real(d_tm, "1/1");
  (void)cvc5_mk_real(d_tm, "-1/-1");
  (void)cvc5_mk_real(d_tm, "1/-1");
  (void)cvc5_mk_real(d_tm, "-1/1");
  ASSERT_DEATH(cvc5_mk_real(nullptr, "123"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_real(d_tm, nullptr), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_real(d_tm, ""), "cannot construct Real");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "asdf"), "cannot construct Real");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "1.2/3"), "cannot construct Real");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "."), "invalid argument '.'");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "/"), "cannot construct Real");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "2/"), "cannot construct Real");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "/2"), "cannot construct Real");
  ASSERT_DEATH(cvc5_mk_real(d_tm, "/-5"), "cannot construct Real");

  (void)cvc5_mk_real_int64(d_tm, 1);
  (void)cvc5_mk_real_int64(d_tm, -1);
  (void)cvc5_mk_real_int64(d_tm, 1);
  ASSERT_DEATH(cvc5_mk_real_int64(nullptr, 1), "unexpected NULL argument");

  (void)cvc5_mk_real_num_den(d_tm, 1, 1);
  (void)cvc5_mk_real_num_den(d_tm, -1, -1);
  (void)cvc5_mk_real_num_den(d_tm, 1, -1);
  (void)cvc5_mk_real_num_den(d_tm, -1, 1);
  (void)cvc5_mk_real_num_den(d_tm, 0, 1);
  ASSERT_DEATH(cvc5_mk_real_num_den(nullptr, 1, 1), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_real_num_den(d_tm, 1, 0), "invalid denominator '0'");
}

TEST_F(TestCApiBlackTermManager, mk_regexp_all)
{
  Cvc5Sort sort = cvc5_get_string_sort(d_tm);
  Cvc5Term s = cvc5_mk_const(d_tm, sort, "s");
  std::vector<Cvc5Term> args = {s, cvc5_mk_regexp_all(d_tm)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_STRING_IN_REGEXP, 2, args.data());
  ASSERT_DEATH(cvc5_mk_regexp_all(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_regexp_allchar)
{
  Cvc5Sort sort = cvc5_get_string_sort(d_tm);
  Cvc5Term s = cvc5_mk_const(d_tm, sort, "s");
  std::vector<Cvc5Term> args = {s, cvc5_mk_regexp_allchar(d_tm)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_STRING_IN_REGEXP, 2, args.data());
  ASSERT_DEATH(cvc5_mk_regexp_allchar(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_regexp_none)
{
  Cvc5Sort sort = cvc5_get_string_sort(d_tm);
  Cvc5Term s = cvc5_mk_const(d_tm, sort, "s");
  std::vector<Cvc5Term> args = {s, cvc5_mk_regexp_none(d_tm)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_STRING_IN_REGEXP, 2, args.data());
  ASSERT_DEATH(cvc5_mk_regexp_none(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_sep_emp)
{
  (void)cvc5_mk_sep_emp(d_tm);
  ASSERT_DEATH(cvc5_mk_sep_emp(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_sep_nil)
{
  (void)cvc5_mk_sep_nil(d_tm, d_bool);
  (void)cvc5_mk_sep_nil(d_tm, d_int);
  ASSERT_DEATH(cvc5_mk_sep_nil(nullptr, d_bool), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_sep_nil(d_tm, nullptr), "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_sep_nil(tm, d_bool);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_string)
{
  (void)cvc5_mk_string(d_tm, "", false);
  (void)cvc5_mk_string(d_tm, "asdfasdf", false);

  ASSERT_EQ(cvc5_term_to_string(cvc5_mk_string(d_tm, "asdf\\nasdf", false)),
            std::string("\"asdf\\u{5c}nasdf\""));
  ASSERT_EQ(
      cvc5_term_to_string(cvc5_mk_string(d_tm, "asdf\\u{005c}nasdf", true)),
      std::string("\"asdf\\u{5c}nasdf\""));
  const wchar_t* s = L"";
  ASSERT_EQ(cvc5_term_get_string_value(cvc5_mk_string_from_wchar(d_tm, s)),
            std::wstring(s));
}

TEST_F(TestCApiBlackTermManager, mk_term)
{
  Cvc5Sort bvsort = cvc5_mk_bv_sort(d_tm, 32);
  Cvc5Term a = cvc5_mk_const(d_tm, bvsort, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, bvsort, "b");

  std::vector<Cvc5Term> args = {};
  std::vector<uint32_t> idxs = {};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_PI, 0, nullptr);
  (void)cvc5_mk_term(d_tm, CVC5_KIND_PI, 0, {});
  (void)cvc5_mk_term(d_tm, CVC5_KIND_PI, 0, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_PI, 0, nullptr), 0, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_PI, 0, idxs.data()), 0, args.data());

  (void)cvc5_mk_term(d_tm, CVC5_KIND_REGEXP_NONE, 0, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_REGEXP_NONE, 0, idxs.data()),
      0,
      args.data());

  (void)cvc5_mk_term(d_tm, CVC5_KIND_REGEXP_ALLCHAR, 0, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_REGEXP_ALLCHAR, 0, idxs.data()),
      0,
      args.data());

  (void)cvc5_mk_term(d_tm, CVC5_KIND_SEP_EMP, 0, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_SEP_EMP, 0, idxs.data()),
      0,
      args.data());

  ASSERT_DEATH(cvc5_mk_term(nullptr, CVC5_KIND_PI, 0, args.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_PI, 1, nullptr),
               "unexpected NULL argument for 'children'");
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_PI, 1, {}),
               "unexpected NULL argument for 'children'");
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_PI, 1, args.data()),
               "unexpected NULL argument for 'children'");
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_CONST_BITVECTOR, 0, args.data()),
               "invalid kind");

  args = {cvc5_mk_true(d_tm)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_NOT, 1, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_NOT, 0, idxs.data()), 1, args.data());
  args = {cvc5_mk_true(d_tm), cvc5_mk_integer_int64(d_tm, 1)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_BAG_MAKE, 2, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_BAG_MAKE, 0, idxs.data()),
      2,
      args.data());
  args = {nullptr};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_NOT, 1, args.data()),
               "invalid term at index 0");
  args = {a};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_NOT, 1, args.data()),
               "expecting a Boolean");

  args = {a, b};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, 2, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_EQUAL, 0, idxs.data()), 2, args.data());
  args = {cvc5_mk_integer_int64(d_tm, 1), cvc5_mk_integer_int64(d_tm, 2)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, 2, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_EQUAL, 0, idxs.data()), 2, args.data());

  ASSERT_DEATH(cvc5_mk_term(nullptr, CVC5_KIND_EQUAL, 2, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_term(nullptr, CVC5_KIND_EQUAL, 2, {}),
               "unexpected NULL argument");
  args = {nullptr, b};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, 2, args.data()),
               "invalid term at index 0");
  args = {a, nullptr};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, 2, args.data()),
               "invalid term at index 1");
  args = {a, cvc5_mk_true(d_tm)};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, 2, args.data()),
               "Subexpressions must have the same type");

  args = {cvc5_mk_true(d_tm), cvc5_mk_true(d_tm), cvc5_mk_true(d_tm)};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_ITE, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_ITE, 0, idxs.data()), 3, args.data());
  args = {nullptr, cvc5_mk_true(d_tm), cvc5_mk_true(d_tm)};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_ITE, 3, args.data()),
               "invalid term at index 0");
  args = {cvc5_mk_true(d_tm), nullptr, cvc5_mk_true(d_tm)};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_ITE, 3, args.data()),
               "invalid term at index 1");
  args = {cvc5_mk_true(d_tm), cvc5_mk_true(d_tm), nullptr};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_ITE, 3, args.data()),
               "invalid term at index 2");
  args = {a, cvc5_mk_true(d_tm), cvc5_mk_true(d_tm)};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_ITE, 3, args.data()),
               "condition of ITE is not Boolean");
  args = {cvc5_mk_true(d_tm), cvc5_mk_true(d_tm), b};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_ITE, 3, args.data()),
               "Branches of the ITE must have comparable type");

  // Test cases that are nary via the API but have arity = 2 internally
  Cvc5Term t_bool = cvc5_mk_const(d_tm, d_bool, "t_bool");
  args = {t_bool, t_bool, t_bool};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_IMPLIES, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_IMPLIES, 0, idxs.data()),
      3,
      args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_XOR, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_XOR, 0, idxs.data()), 3, args.data());

  Cvc5Term t_int = cvc5_mk_const(d_tm, d_int, "t_int");
  args = {t_int, t_int, t_int};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_DIVISION, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_DIVISION, 0, idxs.data()),
      3,
      args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_INTS_DIVISION, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_INTS_DIVISION, 0, idxs.data()),
      3,
      args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_SUB, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_SUB, 0, idxs.data()), 3, args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_EQUAL, 0, idxs.data()), 3, args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_LT, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_LT, 0, idxs.data()), 3, args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_GT, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_GT, 0, idxs.data()), 3, args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_LEQ, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_LEQ, 0, idxs.data()), 3, args.data());
  (void)cvc5_mk_term(d_tm, CVC5_KIND_GEQ, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm, cvc5_mk_op(d_tm, CVC5_KIND_GEQ, 0, idxs.data()), 3, args.data());

  Cvc5Term t_reg = cvc5_mk_const(d_tm, cvc5_get_regexp_sort(d_tm), "t_reg");
  args = {t_reg, t_reg, t_reg};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_REGEXP_DIFF, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_REGEXP_DIFF, 0, idxs.data()),
      3,
      args.data());

  std::vector<Cvc5Sort> domain = {d_bool, d_bool, d_bool};
  Cvc5Term t_fun = cvc5_mk_const(
      d_tm, cvc5_mk_fun_sort(d_tm, 3, domain.data(), d_bool), "t_fun");
  args = {t_fun, t_bool, t_bool, t_bool};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_HO_APPLY, 3, args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_HO_APPLY, 0, idxs.data()),
      3,
      args.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_sep_nil(tm, d_bool);
  args = {t_bool,
          cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), ""),
          cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), "")};
  (void)cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 3, args.data());
  args = {cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), ""),
          t_bool,
          cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), "")};
  (void)cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 3, args.data());
  args = {cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), ""),
          cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), ""),
          t_bool};
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_term_from_op)
{
  Cvc5Sort bvsort = cvc5_mk_bv_sort(d_tm, 32);
  Cvc5Term a = cvc5_mk_const(d_tm, bvsort, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, bvsort, "b");

  (void)cvc5_mk_op(d_tm, CVC5_KIND_PI, 0, {});

  // simple operator terms
  std::vector<uint32_t> idxs = {2, 1};
  Cvc5Op op1 = cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs.data());
  idxs = {1};
  Cvc5Op op2 = cvc5_mk_op(d_tm, CVC5_KIND_DIVISIBLE, 1, idxs.data());

  ASSERT_DEATH(cvc5_mk_op(nullptr, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_op(nullptr, CVC5_KIND_BITVECTOR_EXTRACT, 2, {}),
               "unexpected NULL argument");

  // list datatype
  Cvc5Sort sort = cvc5_mk_param_sort(d_tm, "T");
  std::vector<Cvc5Sort> params = {sort};
  Cvc5DatatypeDecl decl =
      cvc5_mk_dt_decl_with_params(d_tm, "paramlist", 1, params.data(), false);
  Cvc5DatatypeConstructorDecl cons_decl = cvc5_mk_dt_cons_decl(d_tm, "cons");
  Cvc5DatatypeConstructorDecl nil_decl = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_cons_decl_add_selector(cons_decl, "head", sort);
  cvc5_dt_cons_decl_add_selector_self(cons_decl, "tail");
  cvc5_dt_decl_add_constructor(decl, cons_decl);
  cvc5_dt_decl_add_constructor(decl, nil_decl);
  Cvc5Sort dtsort = cvc5_mk_dt_sort(d_tm, decl);
  std::vector<Cvc5Sort> pargs = {d_int};
  Cvc5Sort dtsort_int = cvc5_sort_instantiate(dtsort, 1, pargs.data());
  Cvc5Term c = cvc5_mk_const(d_tm, dtsort_int, "c");
  Cvc5Datatype list = cvc5_sort_get_datatype(dtsort);

  // list datatype constructor and selector operator terms
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor_by_name(list, "cons");
  Cvc5DatatypeConstructor nil = cvc5_dt_get_constructor_by_name(list, "nil");
  Cvc5Term cons_term = cvc5_dt_cons_get_term(cons);
  Cvc5Term nil_term = cvc5_dt_cons_get_term(nil);
  Cvc5Term head_term =
      cvc5_dt_sel_get_term(cvc5_dt_cons_get_selector_by_name(cons, "head"));
  Cvc5Term tail_term =
      cvc5_dt_sel_get_term(cvc5_dt_cons_get_selector_by_name(cons, "tail"));

  // mk_term(_from_op)
  std::vector<Cvc5Term> args = {nil_term};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, 1, args.data());
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, 1, args.data()),
               "");
  args = {cons_term};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, 1, args.data()),
               "");
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, 1, args.data()),
               "");

  args = {head_term};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, 1, args.data()),
               "");

  args = {head_term, c};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, 2, args.data());

  args = {tail_term, c};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, 2, args.data());

  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op1, 0, {}), "");
  args = {a};
  (void)cvc5_mk_term_from_op(d_tm, op1, 1, args.data());
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op2, 1, args.data()), "");
  args = {cvc5_mk_integer_int64(d_tm, 1)};
  (void)cvc5_mk_term_from_op(d_tm, op2, 1, args.data());
  args = {nullptr};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op1, 1, args.data()), "");

  args = {cons_term, cvc5_mk_integer_int64(d_tm, 0)};
  ASSERT_DEATH(cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, 2, args.data()),
               "");
  args = {nil_term};
  args = {cons_term,
          cvc5_mk_integer_int64(d_tm, 0),
          cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, 1, args.data())};
  (void)cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, 3, args.data());

  args = {cvc5_mk_integer_int64(d_tm, 1), cvc5_mk_integer_int64(d_tm, 2)};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op2, 2, args.data()), "");
  args = {a, b};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op1, 2, args.data()), "");
  args = {cvc5_mk_integer_int64(d_tm, 1), nullptr};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op2, 2, args.data()), "");
  args = {nullptr, cvc5_mk_integer_int64(d_tm, 1)};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op2, 2, args.data()), "");

  args = {a, b, a};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op1, 3, args.data()), "");
  args = {
      cvc5_mk_integer_int64(d_tm, 1), cvc5_mk_integer_int64(d_tm, 1), nullptr};
  ASSERT_DEATH(cvc5_mk_term_from_op(d_tm, op2, 3, args.data()), "");

  args = {cvc5_mk_integer_int64(d_tm, 5)};
  (void)cvc5_mk_term_from_op(d_tm, op2, 1, args.data());

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  args = {cvc5_mk_integer_int64(tm, 1)};
  (void)cvc5_mk_term_from_op(tm, op2, 1, args.data());
  idxs = {1};
  (void)cvc5_mk_term_from_op(
      tm, cvc5_mk_op(tm, CVC5_KIND_DIVISIBLE, 1, idxs.data()), 1, args.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_true)
{
  (void)cvc5_mk_true(d_tm);
  ASSERT_DEATH(cvc5_mk_true(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, mk_tuple)
{
  std::vector<Cvc5Term> args = {cvc5_mk_bv(d_tm, 3, "101", 2)};
  (void)cvc5_mk_tuple(d_tm, 1, args.data());
  args = {cvc5_mk_integer(d_tm, "5")};
  (void)cvc5_mk_tuple(d_tm, 1, args.data());
  args = {cvc5_mk_real(d_tm, "5.3")};
  (void)cvc5_mk_tuple(d_tm, 1, args.data());
  ASSERT_DEATH(cvc5_mk_tuple(nullptr, 1, args.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_tuple(nullptr, 0, {}), "unexpected NULL argument");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  args = {cvc5_mk_bv(d_tm, 3, "101", 2)};
  (void)cvc5_mk_tuple(tm, 1, args.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_some)
{
  (void)cvc5_mk_nullable_some(d_tm, cvc5_mk_bv(d_tm, 3, "101", 2));
  (void)cvc5_mk_nullable_some(d_tm, cvc5_mk_integer(d_tm, "5"));
  (void)cvc5_mk_nullable_some(d_tm, cvc5_mk_real(d_tm, "5.3"));
  ASSERT_DEATH(cvc5_mk_nullable_some(nullptr, cvc5_mk_real(d_tm, "5.3")),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_nullable_some(d_tm, nullptr), "invalid term");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_some(tm, cvc5_mk_bv(d_tm, 3, "101", 2));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_val)
{
  Cvc5* solver = cvc5_new(d_tm);
  Cvc5Term value = cvc5_mk_nullable_val(
      d_tm, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5)));
  value = cvc5_simplify(solver, value, false);
  cvc5_delete(solver);

  ASSERT_EQ(5, cvc5_term_get_int64_value(value));
  ASSERT_DEATH(
      cvc5_mk_nullable_val(
          nullptr, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5))),
      "unexpected NULL argument");

  ASSERT_DEATH(cvc5_mk_nullable_val(d_tm, nullptr), "invalid term");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_val(
      tm, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5)));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_is_null)
{
  Cvc5* solver = cvc5_new(d_tm);
  Cvc5Term value = cvc5_mk_nullable_is_null(
      d_tm, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5)));
  value = cvc5_simplify(solver, value, false);
  cvc5_delete(solver);

  ASSERT_EQ(false, cvc5_term_get_boolean_value(value));
  ASSERT_DEATH(
      cvc5_mk_nullable_is_null(
          nullptr, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5))),
      "unexpected NULL argument");

  ASSERT_DEATH(cvc5_mk_nullable_is_null(d_tm, nullptr), "invalid term");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_is_null(
      tm, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5)));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_is_some)
{
  Cvc5* solver = cvc5_new(d_tm);
  Cvc5Term value = cvc5_mk_nullable_is_some(
      d_tm, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5)));
  value = cvc5_simplify(solver, value, false);
  cvc5_delete(solver);

  ASSERT_EQ(true, cvc5_term_get_boolean_value(value));
  ASSERT_DEATH(
      cvc5_mk_nullable_is_some(
          nullptr, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5))),
      "unexpected NULL argument");

  ASSERT_DEATH(cvc5_mk_nullable_is_some(d_tm, nullptr), "invalid term");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_is_some(
      tm, cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 5)));
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_null)
{
  Cvc5* solver = cvc5_new(d_tm);
  Cvc5Sort sort = cvc5_mk_nullable_sort(d_tm, d_bool);
  Cvc5Term null = cvc5_mk_nullable_null(d_tm, sort);
  Cvc5Term value = cvc5_mk_nullable_is_null(d_tm, null);
  value = cvc5_simplify(solver, value, false);
  ASSERT_EQ(true, cvc5_term_get_boolean_value(value));
  cvc5_delete(solver);

  ASSERT_DEATH(cvc5_mk_nullable_null(nullptr, sort),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_nullable_null(d_tm, nullptr), "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_null(tm, sort);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_nullable_lift)
{
  Cvc5* solver = cvc5_new(d_tm);
  Cvc5Term some1 = cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 1));
  Cvc5Term some2 = cvc5_mk_nullable_some(d_tm, cvc5_mk_integer_int64(d_tm, 2));
  std::vector<Cvc5Term> args = {some1, some2};
  Cvc5Term lift = cvc5_mk_nullable_lift(d_tm, CVC5_KIND_ADD, 2, args.data());
  Cvc5Term three =
      cvc5_simplify(solver, cvc5_mk_nullable_val(d_tm, lift), false);
  cvc5_delete(solver);

  ASSERT_EQ(3, cvc5_term_get_int64_value(three));
  ASSERT_DEATH(cvc5_mk_nullable_lift(nullptr, CVC5_KIND_ADD, 2, args.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_nullable_lift(d_tm, CVC5_KIND_ADD, 0, {}),
               "unexpected NULL argument");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_nullable_lift(tm, CVC5_KIND_ADD, 2, args.data());
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_universe_set)
{
  (void)cvc5_mk_universe_set(d_tm, d_bool);
  ASSERT_DEATH(cvc5_mk_universe_set(nullptr, d_bool),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_universe_set(d_tm, nullptr), "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_universe_set(tm, d_bool);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_const)
{
  std::vector<Cvc5Sort> domain = {d_int};
  Cvc5Sort fun_sort = cvc5_mk_fun_sort(d_tm, 1, domain.data(), d_bool);
  (void)cvc5_mk_const(d_tm, d_bool, nullptr);
  (void)cvc5_mk_const(d_tm, fun_sort, nullptr);
  (void)cvc5_mk_const(d_tm, d_bool, "b");
  (void)cvc5_mk_const(d_tm, d_int, "i");
  (void)cvc5_mk_const(d_tm, fun_sort, "f");
  (void)cvc5_mk_const(d_tm, fun_sort, "");
  ASSERT_DEATH(cvc5_mk_const(nullptr, d_bool, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_const(d_tm, nullptr, nullptr), "invalid sort");
  Cvc5TermManager* tm = cvc5_term_manager_new();
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_mk_const(tm, d_bool, nullptr);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackTermManager, mk_skolem)
{
  Cvc5Sort arr_sort = cvc5_mk_array_sort(d_tm, d_int, d_int);
  Cvc5Term a = cvc5_mk_const(d_tm, arr_sort, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, arr_sort, "b");

  std::vector<Cvc5Term> idxs = {a, b};
  Cvc5Term sk = cvc5_mk_skolem(
      d_tm, CVC5_SKOLEM_ID_ARRAY_DEQ_DIFF, idxs.size(), idxs.data());
  idxs = {b, a};
  Cvc5Term sk2 = cvc5_mk_skolem(
      d_tm, CVC5_SKOLEM_ID_ARRAY_DEQ_DIFF, idxs.size(), idxs.data());
  ASSERT_TRUE(cvc5_term_is_skolem(sk));
  ASSERT_TRUE(cvc5_term_is_skolem(sk2));
  ASSERT_EQ(cvc5_term_get_skolem_id(sk), CVC5_SKOLEM_ID_ARRAY_DEQ_DIFF);
  ASSERT_EQ(cvc5_term_get_skolem_id(sk2), CVC5_SKOLEM_ID_ARRAY_DEQ_DIFF);
  size_t size;
  const Cvc5Term* ridxs = cvc5_term_get_skolem_indices(sk, &size);
  ASSERT_EQ(size, 2);
  ASSERT_TRUE(cvc5_term_is_equal(ridxs[0], a));
  ASSERT_TRUE(cvc5_term_is_equal(ridxs[1], b));
  // ARRAY_DEQ_DIFF is commutative, so the order of the indices is sorted.
  ridxs = cvc5_term_get_skolem_indices(sk2, &size);
  ASSERT_EQ(size, 2);
  ASSERT_TRUE(cvc5_term_is_equal(ridxs[0], a));
  ASSERT_TRUE(cvc5_term_is_equal(ridxs[1], b));

  ASSERT_DEATH(
      cvc5_mk_skolem(
          nullptr, CVC5_SKOLEM_ID_ARRAY_DEQ_DIFF, idxs.size(), idxs.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_skolem(d_tm, CVC5_SKOLEM_ID_ARRAY_DEQ_DIFF, 0, nullptr),
               "invalid number of indices");
}

TEST_F(TestCApiBlackTermManager, get_num_idxs_for_skolem_id)
{
  ASSERT_EQ(
      cvc5_get_num_idxs_for_skolem_id(d_tm, CVC5_SKOLEM_ID_BAGS_MAP_INDEX), 5);
  ASSERT_DEATH(
      cvc5_get_num_idxs_for_skolem_id(nullptr, CVC5_SKOLEM_ID_BAGS_MAP_INDEX),
      "unexpected NULL argument");
}

TEST_F(TestCApiBlackTermManager, get_statistics)
{
  ASSERT_DEATH(cvc5_term_manager_get_statistics(nullptr),
               "unexpected NULL argument");

  // do some array reasoning to make sure we have a double statistics
  Cvc5* solver = cvc5_new(d_tm);
  Cvc5Sort s2 = cvc5_mk_array_sort(d_tm, d_int, d_int);
  Cvc5Term t1 = cvc5_mk_const(d_tm, d_int, "i");
  Cvc5Term t2 = cvc5_mk_const(d_tm, s2, "a");
  std::vector<Cvc5Term> args = {t2, t1};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_SELECT, args.size(), args.data()), t1};
  cvc5_assert_formula(
      solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(solver);

  Cvc5Statistics stats = cvc5_term_manager_get_statistics(d_tm);
  (void)cvc5_stats_to_string(stats);

  cvc5_stats_iter_init(stats, true, true);
  bool hasstats = false;
  while (cvc5_stats_iter_has_next(stats))
  {
    hasstats = true;
    const char* name;
    Cvc5Stat stat = cvc5_stats_iter_next(stats, &name);
    (void)cvc5_stat_to_string(stat);
    if (name == std::string("cvc5::CONSTANT"))
    {
      ASSERT_FALSE(cvc5_stat_is_internal(stat));
      ASSERT_FALSE(cvc5_stat_is_default(stat));
      ASSERT_TRUE(cvc5_stat_is_histogram(stat));
      const char** keys;
      uint64_t* values;
      size_t size;
      cvc5_stat_get_histogram(stat, &keys, &values, &size);
      ASSERT_NE(size, 0);
      ASSERT_EQ(cvc5_stat_to_string(stat),
                std::string("{ UNKNOWN_TYPE_CONSTANT: 1, integer type: 1 }"));
    }
  }
  ASSERT_TRUE(hasstats);
  cvc5_delete(solver);
}

TEST_F(TestCApiBlackTermManager, print_statistics_safe)
{
  testing::internal::CaptureStdout();
  cvc5_term_manager_print_stats_safe(d_tm, STDOUT_FILENO);
  std::stringstream expected;
  expected << "cvc5::CONSTANT = { integer type: 1, UNKNOWN_TYPE_CONSTANT: 1 }"
           << std::endl
           << "cvc5::TERM = { <unsupported>: 1 }" << std::endl;
  testing::internal::GetCapturedStdout();
}

}  // namespace cvc5::internal::test
