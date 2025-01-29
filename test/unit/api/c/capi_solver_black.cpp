/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Hans-Joerg Schurr, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of solver functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <cmath>
#include <fstream>

#include "base/check.h"
#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackSolver : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_int = cvc5_get_integer_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
    d_str = cvc5_get_string_sort(d_tm);
    d_uninterpreted = cvc5_mk_uninterpreted_sort(d_tm, "u");
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }

  /**
   * Helper function for testGetSeparation{Heap,Nil}TermX. Asserts and checks
   * some simple separation logic constraints.
   */
  void check_simple_separation_constraints()
  {
    // declare the separation heap
    cvc5_declare_sep_heap(d_solver, d_int, d_int);
    Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
    Cvc5Term p = cvc5_mk_const(d_tm, d_int, "p");
    std::vector<Cvc5Term> args = {p, x};
    Cvc5Term heap =
        cvc5_mk_term(d_tm, CVC5_KIND_SEP_PTO, args.size(), args.data());
    cvc5_assert_formula(d_solver, heap);
    Cvc5Term nil = cvc5_mk_sep_nil(d_tm, d_int);
    args = {nil, cvc5_mk_integer_int64(d_tm, 5)};
    cvc5_assert_formula(
        d_solver,
        cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
    cvc5_check_sat(d_solver);
  }

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5Sort d_bool;
  Cvc5Sort d_int;
  Cvc5Sort d_real;
  Cvc5Sort d_str;
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackSolver, pow2_large1)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/371
  Cvc5Sort s4 = cvc5_mk_array_sort(d_tm, d_str, d_int);
  Cvc5Sort s7 = cvc5_mk_array_sort(d_tm, d_int, d_str);
  Cvc5Term t10 = cvc5_mk_integer(d_tm, "68038927088685865242724985643");
  Cvc5Term t74 = cvc5_mk_integer(d_tm, "8416288636405");
  Cvc5DatatypeConstructorDecl cons1 = cvc5_mk_dt_cons_decl(d_tm, "_x109");
  cvc5_dt_cons_decl_add_selector(cons1, "_x108", s7);
  Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(d_tm, "_x113");
  cvc5_dt_cons_decl_add_selector(cons2, "_x110", s4);
  cvc5_dt_cons_decl_add_selector(cons2, "_x111", d_int);
  cvc5_dt_cons_decl_add_selector(cons2, "_x112", s7);
  std::vector<Cvc5DatatypeConstructorDecl> ctors = {cons1, cons2};
  Cvc5Sort s11 = cvc5_declare_dt(d_solver, "_x107", ctors.size(), ctors.data());
  Cvc5Term t82 = cvc5_mk_const(d_tm, s11, "_x114");
  std::vector<Cvc5Term> args = {t10};
  Cvc5Term t180 = cvc5_mk_term(d_tm, CVC5_KIND_POW2, args.size(), args.data());
  args = {t74, t180};
  Cvc5Term t258 = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  cvc5_assert_formula(d_solver, t258);
  ASSERT_DEATH(cvc5_simplify(d_solver, t82, true),
               "can only be a positive integral constant below");
}

TEST_F(TestCApiBlackSolver, pow2_large2)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/333
  Cvc5Term t1 = cvc5_mk_bv_uint64(d_tm, 63, ~(((uint64_t)1) << 62));
  std::vector<Cvc5Term> args = {t1};
  Cvc5Term t2 =
      cvc5_mk_term(d_tm, CVC5_KIND_BITVECTOR_TO_NAT, args.size(), args.data());
  args = {t2};
  Cvc5Term t3 = cvc5_mk_term(d_tm, CVC5_KIND_POW2, args.size(), args.data());
  args = {t3, t2};
  Cvc5Term t4 =
      cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data());
  std::vector<Cvc5Term> assumptions = {t4};
  ASSERT_DEATH(
      cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data()),
      "can only be a positive integral constant below");
}

TEST_F(TestCApiBlackSolver, pow2_large3)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/339
  Cvc5Term t203 = cvc5_mk_integer(d_tm, "6135470354240554220207");
  std::vector<Cvc5Term> args = {t203};
  Cvc5Term t262 = cvc5_mk_term(d_tm, CVC5_KIND_POW2, args.size(), args.data());
  args = {t262};
  std::vector<uint32_t> idxs = {49};
  Cvc5Term t536 = cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(d_tm, CVC5_KIND_INT_TO_BITVECTOR, idxs.size(), idxs.data()),
      args.size(),
      args.data());
  // should not throw an exception, will not simplify.
  cvc5_simplify(d_solver, t536, false);
}

TEST_F(TestCApiBlackSolver, simplify)
{
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {bv_sort, bv_sort};
  Cvc5Sort fun_sort1 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), bv_sort);
  domain = {d_uninterpreted};
  Cvc5Sort fun_sort2 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", d_int);
  cvc5_dt_cons_decl_add_selector_self(cons, "tail");
  cvc5_dt_decl_add_constructor(decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);
  Cvc5Sort list = cvc5_mk_dt_sort(d_tm, decl);

  Cvc5Term x = cvc5_mk_const(d_tm, bv_sort, "x");
  (void)cvc5_simplify(d_solver, x, false);

  ASSERT_DEATH(cvc5_simplify(nullptr, x, false), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_simplify(d_solver, nullptr, false), "invalid term");

  Cvc5Term a = cvc5_mk_const(d_tm, bv_sort, "a");
  (void)cvc5_simplify(d_solver, a, false);
  Cvc5Term b = cvc5_mk_const(d_tm, bv_sort, "b");
  (void)cvc5_simplify(d_solver, b, false);
  std::vector<Cvc5Term> args = {x, x};
  Cvc5Term x_eq_x =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  (void)cvc5_simplify(d_solver, x_eq_x, false);
  ASSERT_TRUE(cvc5_term_is_disequal(cvc5_mk_true(d_tm), x_eq_x));
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_mk_true(d_tm),
                                 cvc5_simplify(d_solver, x_eq_x, false)));
  args = {x, b};
  Cvc5Term x_eq_b =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  (void)cvc5_simplify(d_solver, x_eq_b, false);
  ASSERT_TRUE(cvc5_term_is_disequal(cvc5_mk_true(d_tm), x_eq_b));
  ASSERT_TRUE(cvc5_term_is_disequal(cvc5_mk_true(d_tm),
                                    cvc5_simplify(d_solver, x_eq_b, false)));

  Cvc5Term i1 = cvc5_mk_const(d_tm, d_int, "i1");
  (void)cvc5_simplify(d_solver, i1, false);
  args = {i1, cvc5_mk_integer(d_tm, "23")};
  Cvc5Term i2 = cvc5_mk_term(d_tm, CVC5_KIND_MULT, args.size(), args.data());
  (void)cvc5_simplify(d_solver, i2, false);
  ASSERT_TRUE(cvc5_term_is_disequal(i1, i2));
  ASSERT_TRUE(cvc5_term_is_disequal(i1, cvc5_simplify(d_solver, i2, false)));

  args = {i1, cvc5_mk_integer(d_tm, "0")};
  Cvc5Term i3 = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  (void)cvc5_simplify(d_solver, i3, false);
  ASSERT_TRUE(cvc5_term_is_disequal(i1, i3));
  ASSERT_TRUE(cvc5_term_is_equal(i1, cvc5_simplify(d_solver, i3, false)));

  Cvc5Datatype list_dt = cvc5_sort_get_datatype(list);
  args = {
      cvc5_dt_cons_get_term(cvc5_dt_get_constructor_by_name(list_dt, "nil"))};
  args = {
      cvc5_dt_cons_get_term(cvc5_dt_get_constructor_by_name(list_dt, "cons")),
      cvc5_mk_integer(d_tm, "0"),
      cvc5_mk_term(
          d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, args.size(), args.data())};
  Cvc5Term dt1 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, args.size(), args.data());
  (void)cvc5_simplify(d_solver, dt1, false);

  args = {cvc5_dt_sel_get_term(cvc5_dt_cons_get_selector_by_name(
              cvc5_dt_get_constructor_by_name(list_dt, "cons"), "head")),
          dt1};
  Cvc5Term dt2 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, args.size(), args.data());
  (void)cvc5_simplify(d_solver, dt2, false);

  Cvc5Term b1 = cvc5_mk_var(d_tm, bv_sort, "b1");
  (void)cvc5_simplify(d_solver, b1, false);
  Cvc5Term b2 = cvc5_mk_var(d_tm, bv_sort, "b1");
  (void)cvc5_simplify(d_solver, b2, false);
  Cvc5Term b3 = cvc5_mk_var(d_tm, d_uninterpreted, "b3");
  (void)cvc5_simplify(d_solver, b3, false);
  Cvc5Term v1 = cvc5_mk_const(d_tm, bv_sort, "v1");
  (void)cvc5_simplify(d_solver, v1, false);
  Cvc5Term v2 = cvc5_mk_const(d_tm, d_int, "v2");
  (void)cvc5_simplify(d_solver, v2, false);
  Cvc5Term f1 = cvc5_mk_const(d_tm, fun_sort1, "f1");
  (void)cvc5_simplify(d_solver, f1, false);
  Cvc5Term f2 = cvc5_mk_const(d_tm, fun_sort2, "f1");
  (void)cvc5_simplify(d_solver, f2, false);

  std::vector<Cvc5Term> funs = {f1, f2};
  std::vector<size_t> nvars = {2, 1};
  std::vector<Cvc5Term> vars1 = {b1, b2};
  std::vector<Cvc5Term> vars2 = {b3};
  std::vector<const Cvc5Term*> vars = {vars1.data(), vars2.data()};
  std::vector<Cvc5Term> terms = {v1, v2};
  cvc5_define_funs_rec(d_solver,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  (void)cvc5_simplify(d_solver, f1, false);
  (void)cvc5_simplify(d_solver, f2, false);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_simplify(slv, x, false);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, simplify_apply_subs)
{
  cvc5_set_option(d_solver, "incremental", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  std::vector<Cvc5Term> args = {x, zero};
  Cvc5Term eq = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  cvc5_assert_formula(d_solver, eq);
  cvc5_check_sat(d_solver);

  ASSERT_TRUE(cvc5_term_is_equal(cvc5_simplify(d_solver, x, false), x));
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_simplify(d_solver, x, true), zero));
}

TEST_F(TestCApiBlackSolver, assert_formula)
{
  ASSERT_DEATH(cvc5_assert_formula(nullptr, cvc5_mk_true(d_tm)),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_assert_formula(d_solver, nullptr), "invalid term");

  cvc5_assert_formula(d_solver, cvc5_mk_true(d_tm));

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_assert_formula(slv, cvc5_mk_true(d_tm));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, check_sat)
{
  ASSERT_DEATH(cvc5_check_sat(nullptr), "unexpected NULL argument");

  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_check_sat(d_solver), "cannot make multiple queries");
}

TEST_F(TestCApiBlackSolver, check_sat_assuming)
{
  std::vector<Cvc5Term> assumptions = {nullptr};
  ASSERT_DEATH(
      cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data()),
      "invalid term at index 0");
  assumptions = {cvc5_mk_true(d_tm)};
  ASSERT_DEATH(
      cvc5_check_sat_assuming(nullptr, assumptions.size(), assumptions.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(cvc5_check_sat_assuming(d_solver, 0, nullptr),
               "unexpected NULL argument");

  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  ASSERT_DEATH(
      cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data()),
      "cannot make multiple queries");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_check_sat_assuming(slv, assumptions.size(), assumptions.data());
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, check_sat_assuming1)
{
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_bool, "y");
  std::vector<Cvc5Term> args = {x, y};
  Cvc5Term z = cvc5_mk_term(d_tm, CVC5_KIND_AND, args.size(), args.data());
  cvc5_set_option(d_solver, "incremental", "true");
  std::vector<Cvc5Term> assumptions = {cvc5_mk_true(d_tm)};
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  assumptions = {z};
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
}

TEST_F(TestCApiBlackSolver, check_sat_assuming2)
{
  cvc5_set_option(d_solver, "incremental", "true");

  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort u_to_int_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort int_pred_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  // Constants
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  // Functions
  Cvc5Term f = cvc5_mk_const(d_tm, u_to_int_sort, "f");
  Cvc5Term p = cvc5_mk_const(d_tm, int_pred_sort, "p");
  // Values
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  // Terms
  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  // Assertions
  args = {zero, f_x};
  Cvc5Term args1 = cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data());
  args = {zero, f_y};
  Cvc5Term args2 = cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data());
  args = {sum, one};
  Cvc5Term args3 = cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data());
  args = {p_0};
  args = {args1,
          args2,
          args3,
          cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()),
          p_f_y};
  Cvc5Term assertions =
      cvc5_mk_term(d_tm, CVC5_KIND_AND, args.size(), args.data());

  std::vector<Cvc5Term> assumptions = {cvc5_mk_true(d_tm)};
  (void)cvc5_check_sat_assuming(
      d_solver, assumptions.size(), assumptions.data());
  cvc5_assert_formula(d_solver, assertions);
  args = {x, y};
  Cvc5Term dist =
      cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data());
  assumptions = {dist};
  (void)cvc5_check_sat_assuming(
      d_solver, assumptions.size(), assumptions.data());
  assumptions = {cvc5_mk_false(d_tm), dist};
}

TEST_F(TestCApiBlackSolver, declare_datatype)
{
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "lin");
  std::vector<Cvc5DatatypeConstructorDecl> ctors = {nil};
  (void)cvc5_declare_dt(d_solver, "", ctors.size(), ctors.data());

  nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  ctors = {nil};
  (void)cvc5_declare_dt(d_solver, "a", ctors.size(), ctors.data());

  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  ctors = {cons, nil};
  (void)cvc5_declare_dt(d_solver, "b", ctors.size(), ctors.data());

  cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  ctors = {cons, nil};
  (void)cvc5_declare_dt(d_solver, "", ctors.size(), ctors.data());

  cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  ctors = {cons, nil};
  ASSERT_DEATH(cvc5_declare_dt(nullptr, "c", ctors.size(), ctors.data()),
               "unexpected NULL argument");
  ctors = {nullptr};
  ASSERT_DEATH(cvc5_declare_dt(d_solver, "c", ctors.size(), ctors.data()),
               "invalid datatype constructor declaration at index 0");

  // must have at least one constructor
  ctors = {};
  ASSERT_DEATH(cvc5_declare_dt(d_solver, "c", ctors.size(), ctors.data()),
               "expected a datatype declaration with at least one constructor");
  // constructors may not be reused
  Cvc5DatatypeConstructorDecl ctor1 = cvc5_mk_dt_cons_decl(d_tm, "_x21");
  Cvc5DatatypeConstructorDecl ctor2 = cvc5_mk_dt_cons_decl(d_tm, "_x31");
  ctors = {ctor1, ctor2};
  (void)cvc5_declare_dt(d_solver, "_x17", ctors.size(), ctors.data());
  ASSERT_DEATH(cvc5_declare_dt(d_solver, "_x86", ctors.size(), ctors.data()),
               "cannot use a constructor for multiple datatypes");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  ctors = {nil};
  (void)cvc5_declare_dt(d_solver, "a", ctors.size(), ctors.data());
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, dt_get_arity)
{
  std::vector<Cvc5DatatypeConstructorDecl> ctors = {
      cvc5_mk_dt_cons_decl(d_tm, "_x21"), cvc5_mk_dt_cons_decl(d_tm, "_x31")};
  Cvc5Sort s3 = cvc5_declare_dt(d_solver, "_x17", ctors.size(), ctors.data());
  ASSERT_EQ(cvc5_sort_dt_get_arity(s3), 0);
}

TEST_F(TestCApiBlackSolver, declare_fun)
{
  ASSERT_DEATH(cvc5_declare_fun(nullptr, "b", 0, nullptr, d_bool, true),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_fun(d_solver, "b", 0, nullptr, nullptr, true),
               "invalid sort");

  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  (void)cvc5_declare_fun(d_solver, "f1", 0, nullptr, bv_sort, true);
  domain = {bv_sort, d_int};
  (void)cvc5_declare_fun(
      d_solver, "f3", domain.size(), domain.data(), bv_sort, true);
  ASSERT_DEATH(cvc5_declare_fun(d_solver, "f3", 0, nullptr, fun_sort, true),
               "invalid argument");
  // functions as arguments is allowed
  domain = {bv_sort, fun_sort};
  (void)cvc5_declare_fun(
      d_solver, "f4", domain.size(), domain.data(), bv_sort, true);
  domain = {bv_sort, bv_sort};
  ASSERT_DEATH(
      cvc5_declare_fun(
          d_solver, "f5", domain.size(), domain.data(), fun_sort, true),
      "invalid argument");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_declare_fun(slv, "f1", 0, nullptr, bv_sort, true);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, declare_fun_fresh)
{
  // std::vector<Cvc5Sort> domain =
  Cvc5Term t1 = cvc5_declare_fun(d_solver, "b", 0, nullptr, d_bool, true);
  Cvc5Term t2 = cvc5_declare_fun(d_solver, "b", 0, nullptr, d_bool, false);
  Cvc5Term t3 = cvc5_declare_fun(d_solver, "b", 0, nullptr, d_bool, false);
  ASSERT_FALSE(cvc5_term_is_equal(t1, t2));
  ASSERT_FALSE(cvc5_term_is_equal(t1, t3));
  ASSERT_TRUE(cvc5_term_is_equal(t2, t3));
  Cvc5Term t4 = cvc5_declare_fun(d_solver, "c", 0, nullptr, d_bool, false);
  ASSERT_FALSE(cvc5_term_is_equal(t2, t4));
  Cvc5Term t5 = cvc5_declare_fun(d_solver, "b", 0, nullptr, d_int, false);
  ASSERT_FALSE(cvc5_term_is_equal(t2, t5));

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_declare_fun(slv, "b", 0, nullptr, d_int, false);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, declare_sort)
{
  ASSERT_DEATH(cvc5_declare_sort(nullptr, "s", 0, true),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_sort(d_solver, nullptr, 0, true),
               "unexpected NULL argument");
  (void)cvc5_declare_sort(d_solver, "s", 0, true);
  (void)cvc5_declare_sort(d_solver, "s", 2, true);
  (void)cvc5_declare_sort(d_solver, "", 2, true);
}

TEST_F(TestCApiBlackSolver, declare_sort_fresh)
{
  ASSERT_DEATH(cvc5_declare_sort(nullptr, "b", 0, true),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_sort(d_solver, nullptr, 0, true),
               "unexpected NULL argument");

  Cvc5Sort s1 = cvc5_declare_sort(d_solver, "b", 0, true);
  Cvc5Sort s2 = cvc5_declare_sort(d_solver, "b", 0, false);
  Cvc5Sort s3 = cvc5_declare_sort(d_solver, "b", 0, false);
  ASSERT_FALSE(cvc5_sort_is_equal(s1, s2));
  ASSERT_FALSE(cvc5_sort_is_equal(s1, s3));
  ASSERT_TRUE(cvc5_sort_is_equal(s2, s3));

  Cvc5Sort s4 = cvc5_declare_sort(d_solver, "c", 0, false);
  ASSERT_FALSE(cvc5_sort_is_equal(s2, s4));

  Cvc5Sort s5 = cvc5_declare_sort(d_solver, "b", 1, false);
  ASSERT_FALSE(cvc5_sort_is_equal(s2, s5));
}

TEST_F(TestCApiBlackSolver, define_fun)
{
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  Cvc5Term b1 = cvc5_mk_var(d_tm, bv_sort, "b1");
  Cvc5Term b2 = cvc5_mk_var(d_tm, d_int, "b2");
  Cvc5Term b3 = cvc5_mk_var(d_tm, fun_sort, "b3");
  Cvc5Term v1 = cvc5_mk_const(d_tm, bv_sort, "v1");
  Cvc5Term v2 = cvc5_mk_const(d_tm, fun_sort, "v2");

  ASSERT_DEATH(cvc5_define_fun(nullptr, "f", 0, nullptr, bv_sort, v1, false),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_define_fun(d_solver, "f", 0, nullptr, nullptr, v1, false),
               "invalid sort");
  ASSERT_DEATH(
      cvc5_define_fun(d_solver, "f", 0, nullptr, bv_sort, nullptr, false),
      "invalid term");

  (void)cvc5_define_fun(d_solver, "f", 0, nullptr, bv_sort, v1, false);
  std::vector<Cvc5Term> vars = {b1, b2};
  (void)cvc5_define_fun(
      d_solver, "f", vars.size(), vars.data(), bv_sort, v1, false);
  vars = {v1, b2};
  ASSERT_DEATH(cvc5_define_fun(
                   d_solver, "f", vars.size(), vars.data(), bv_sort, v1, false),
               "invalid bound variable");
  vars = {b1};
  ASSERT_DEATH(cvc5_define_fun(
                   d_solver, "f", vars.size(), vars.data(), bv_sort, v2, false),
               "invalid sort of function body");
  ASSERT_DEATH(
      cvc5_define_fun(
          d_solver, "f", vars.size(), vars.data(), fun_sort, v2, false),
      "invalid argument");
  // b3 has function sort, which is allowed as an argument
  vars = {b1, b3};
  (void)cvc5_define_fun(
      d_solver, "f", vars.size(), vars.data(), bv_sort, v1, false);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  Cvc5Sort bv_sort2 = cvc5_mk_bv_sort(tm, 32);
  Cvc5Term v12 = cvc5_mk_const(tm, bv_sort2, "v1");
  Cvc5Term b12 = cvc5_mk_var(d_tm, bv_sort2, "b1");
  Cvc5Term b22 = cvc5_mk_var(d_tm, cvc5_get_integer_sort(tm), "b2");
  vars = {};
  (void)cvc5_define_fun(
      slv, "f", vars.size(), vars.data(), bv_sort, v12, false);
  (void)cvc5_define_fun(
      slv, "f", vars.size(), vars.data(), bv_sort2, v1, false);
  vars = {b1, b22};
  (void)cvc5_define_fun(
      slv, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  vars = {b12, b2};
  (void)cvc5_define_fun(
      slv, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  vars = {b12, b22};
  (void)cvc5_define_fun(
      slv, "f", vars.size(), vars.data(), bv_sort, v12, false);
  (void)cvc5_define_fun(
      slv, "f", vars.size(), vars.data(), bv_sort2, v1, false);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, define_fun_global)
{
  Cvc5Term btrue = cvc5_mk_true(d_tm);
  // (define-fun f () Bool true)
  Cvc5Term f = cvc5_define_fun(d_solver, "f", 0, nullptr, d_bool, btrue, true);
  Cvc5Term b = cvc5_mk_var(d_tm, d_bool, "b");
  // (define-fun g (b Bool) Bool b)
  std::vector<Cvc5Term> vars = {b};
  Cvc5Term g =
      cvc5_define_fun(d_solver, "g", vars.size(), vars.data(), d_bool, b, true);

  // (assert (or (not f) (not (g true))))
  std::vector<Cvc5Term> args = {f};
  Cvc5Term fnot = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  args = {g, btrue};
  Cvc5Term app =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {app};
  Cvc5Term appnot = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());

  args = {fnot, appnot};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));

  cvc5_reset_assertions(d_solver);
  cvc5_result_release(res);
  // (assert (or (not f) (not (g true))))
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));
}

TEST_F(TestCApiBlackSolver, define_fun_rec)
{
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {bv_sort, bv_sort};
  Cvc5Sort fun_sort1 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), bv_sort);
  domain = {d_uninterpreted};
  Cvc5Sort fun_sort2 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  Cvc5Term b1 = cvc5_mk_var(d_tm, bv_sort, "b1");
  Cvc5Term b11 = cvc5_mk_var(d_tm, bv_sort, "b1");
  Cvc5Term b2 = cvc5_mk_var(d_tm, d_int, "b2");
  Cvc5Term b3 = cvc5_mk_var(d_tm, fun_sort2, "b3");
  Cvc5Term v1 = cvc5_mk_const(d_tm, bv_sort, "v1");
  Cvc5Term v2 = cvc5_mk_const(d_tm, d_int, "v1");
  Cvc5Term v3 = cvc5_mk_const(d_tm, fun_sort2, "v3");
  Cvc5Term f1 = cvc5_mk_const(d_tm, fun_sort1, "f1");
  Cvc5Term f2 = cvc5_mk_const(d_tm, fun_sort2, "f2");
  Cvc5Term f3 = cvc5_mk_const(d_tm, bv_sort, "f3");

  (void)cvc5_define_fun_rec(d_solver, "f", 0, nullptr, bv_sort, v1, false);
  std::vector<Cvc5Term> vars = {b1, b2};
  (void)cvc5_define_fun_rec(
      d_solver, "f", vars.size(), vars.data(), bv_sort, v1, false);
  vars = {b1, b11};
  (void)cvc5_define_fun_rec_from_const(
      d_solver, f1, vars.size(), vars.data(), v1, false);

  // b3 has function sort, which is allowed as an argument
  vars = {b1, b3};
  (void)cvc5_define_fun_rec(
      d_solver, "f", vars.size(), vars.data(), bv_sort, v1, false);

  ASSERT_DEATH(
      cvc5_define_fun_rec(nullptr, "f", 0, nullptr, bv_sort, v1, false),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_define_fun_rec(d_solver, nullptr, 0, nullptr, bv_sort, v1, false),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_define_fun_rec(d_solver, "f", 0, nullptr, nullptr, v1, false),
      "invalid sort");
  ASSERT_DEATH(
      cvc5_define_fun_rec(d_solver, "f", 0, nullptr, bv_sort, nullptr, false),
      "invalid term");

  vars = {b1};
  ASSERT_DEATH(cvc5_define_fun_rec(
                   d_solver, "f", vars.size(), vars.data(), bv_sort, v3, false),
               "invalid sort");
  vars = {b1, v2};
  ASSERT_DEATH(cvc5_define_fun_rec(
                   d_solver, "f", vars.size(), vars.data(), bv_sort, v1, false),
               "invalid bound variable");
  vars = {b1};
  ASSERT_DEATH(
      cvc5_define_fun_rec(
          d_solver, "f", vars.size(), vars.data(), fun_sort2, v3, false),
      "invalid argument");

  ASSERT_DEATH(
      cvc5_define_fun_rec_from_const(nullptr, f1, 0, nullptr, v1, false),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_define_fun_rec_from_const(d_solver, nullptr, 0, nullptr, v1, false),
      "invalid term");
  ASSERT_DEATH(
      cvc5_define_fun_rec_from_const(d_solver, f1, 0, nullptr, nullptr, false),
      "invalid term");

  vars = {b1};
  ASSERT_DEATH(cvc5_define_fun_rec_from_const(
                   d_solver, f1, vars.size(), vars.data(), v1, false),
               "invalid size of argument 'bound_vars'");
  ASSERT_DEATH(cvc5_define_fun_rec_from_const(
                   d_solver, f2, vars.size(), vars.data(), v2, false),
               "invalid sort");
  ASSERT_DEATH(cvc5_define_fun_rec_from_const(
                   d_solver, f3, vars.size(), vars.data(), v1, false),
               "invalid argument");
  vars = {b1, b11};
  ASSERT_DEATH(cvc5_define_fun_rec_from_const(
                   d_solver, f1, vars.size(), vars.data(), v2, false),
               "invalid sort");
  ASSERT_DEATH(cvc5_define_fun_rec_from_const(
                   d_solver, f1, vars.size(), vars.data(), v3, false),
               "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  Cvc5Sort bv_sort2 = cvc5_mk_bv_sort(tm, 32);
  Cvc5Term b12 = cvc5_mk_var(tm, bv_sort, "b1");
  Cvc5Term b22 = cvc5_mk_var(tm, d_int, "b2");
  Cvc5Term v12 = cvc5_mk_const(tm, bv_sort, "v1");
  vars = {};
  (void)cvc5_define_fun_rec(
      d_solver, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort, v12, false);
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort2, v1, false);
  vars = {b12, b22};
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  vars = {b12, b22};
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  vars = {b1, b22};
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  vars = {b12, b2};
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort2, v12, false);
  vars = {b12, b22};
  (void)cvc5_define_fun_rec(
      slv, "f", vars.size(), vars.data(), bv_sort2, v1, false);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, define_fun_rec_wrong_logic)
{
  cvc5_set_logic(d_solver, "QF_BV");
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {bv_sort, bv_sort};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), bv_sort);
  Cvc5Term b = cvc5_mk_var(d_tm, bv_sort, "b");
  Cvc5Term v = cvc5_mk_var(d_tm, bv_sort, "v");
  Cvc5Term f = cvc5_mk_var(d_tm, fun_sort, "f");
  std::vector<Cvc5Term> vars = {};
  ASSERT_DEATH(cvc5_define_fun_rec(
                   d_solver, "f", vars.size(), vars.data(), bv_sort, v, false),
               "require a logic with quantifiers");
  vars = {b, b};
  ASSERT_DEATH(cvc5_define_fun_rec_from_const(
                   d_solver, f, vars.size(), vars.data(), v, false),
               "require a logic with quantifiers");
}

TEST_F(TestCApiBlackSolver, define_fun_rec_global)
{
  cvc5_push(d_solver, 1);
  Cvc5Term btrue = cvc5_mk_true(d_tm);
  // (define-fun f () Bool true)
  Cvc5Term f =
      cvc5_define_fun_rec(d_solver, "f", 0, nullptr, d_bool, btrue, true);
  Cvc5Term b = cvc5_mk_var(d_tm, d_bool, "b");
  // (define-fun g (b Bool) Bool b)
  std::vector<Cvc5Sort> domain = {d_bool};
  Cvc5Term ff = cvc5_mk_const(
      d_tm, cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool), "g");
  std::vector<Cvc5Term> vars = {b};
  Cvc5Term g = cvc5_define_fun_rec_from_const(
      d_solver, ff, vars.size(), vars.data(), b, true);

  // (assert (or (not f) (not (g true))))
  std::vector<Cvc5Term> args = {f};
  Cvc5Term fnot = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  args = {g, btrue};
  Cvc5Term app =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {app};
  Cvc5Term appnot = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  args = {fnot, appnot};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));
  cvc5_pop(d_solver, 1);
  // (assert (or (not f) (not (g true))))
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  Cvc5Term bb = cvc5_mk_var(tm, cvc5_get_boolean_sort(tm), "b");
  domain = {d_bool};
  vars = {bb};
  (void)cvc5_define_fun_rec_from_const(
      slv,
      cvc5_mk_const(
          d_tm,
          cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool),
          "g"),
      vars.size(),
      vars.data(),
      bb,
      true);
  vars = {b};
  (void)cvc5_define_fun_rec_from_const(
      slv,
      cvc5_mk_const(
          tm, cvc5_mk_fun_sort(tm, domain.size(), domain.data(), d_bool), "g"),
      vars.size(),
      vars.data(),
      bb,
      true);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, define_funs_rec)
{
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {bv_sort, bv_sort};
  Cvc5Sort fun_sort1 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), bv_sort);
  domain = {d_uninterpreted};
  Cvc5Sort fun_sort2 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  Cvc5Term b1 = cvc5_mk_var(d_tm, bv_sort, "b1");
  Cvc5Term b11 = cvc5_mk_var(d_tm, bv_sort, "b1");
  Cvc5Term b2 = cvc5_mk_var(d_tm, d_int, "b2");
  Cvc5Term b4 = cvc5_mk_var(d_tm, d_uninterpreted, "b4");
  Cvc5Term v1 = cvc5_mk_const(d_tm, bv_sort, "v1");
  Cvc5Term v2 = cvc5_mk_const(d_tm, d_int, "v2");
  Cvc5Term v4 = cvc5_mk_const(d_tm, d_uninterpreted, "v4");
  Cvc5Term f1 = cvc5_mk_const(d_tm, fun_sort1, "f1");
  Cvc5Term f2 = cvc5_mk_const(d_tm, fun_sort2, "f2");
  Cvc5Term f3 = cvc5_mk_const(d_tm, bv_sort, "f3");

  std::vector<Cvc5Term> funs = {f1, f2};
  std::vector<size_t> nvars = {2, 1};
  std::vector<Cvc5Term> vars1 = {b1, b11};
  std::vector<Cvc5Term> vars2 = {b4};
  std::vector<const Cvc5Term*> vars = {vars1.data(), vars2.data()};
  std::vector<Cvc5Term> terms = {v1, v2};

  cvc5_define_funs_rec(d_solver,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  vars1 = {v1, b11};
  vars = {vars1.data(), vars2.data()};
  ASSERT_DEATH(cvc5_define_funs_rec(d_solver,
                                    funs.size(),
                                    funs.data(),
                                    nvars.data(),
                                    vars.data(),
                                    terms.data(),
                                    false),
               "invalid bound variable");
  funs = {f1, f3};
  vars1 = {b1, b11};
  vars = {vars1.data(), vars2.data()};
  ASSERT_DEATH(cvc5_define_funs_rec(d_solver,
                                    funs.size(),
                                    funs.data(),
                                    nvars.data(),
                                    vars.data(),
                                    terms.data(),
                                    false),
               "invalid argument");
  funs = {f1, f2};
  vars1 = {b1};
  vars = {vars1.data(), vars2.data()};
  nvars = {1, 1};
  ASSERT_DEATH(cvc5_define_funs_rec(d_solver,
                                    funs.size(),
                                    funs.data(),
                                    nvars.data(),
                                    vars.data(),
                                    terms.data(),
                                    false),
               "invalid size of argument");
  vars1 = {b1, b2};
  vars = {vars1.data(), vars2.data()};
  nvars = {2, 1};
  ASSERT_DEATH(cvc5_define_funs_rec(d_solver,
                                    funs.size(),
                                    funs.data(),
                                    nvars.data(),
                                    vars.data(),
                                    terms.data(),
                                    false),
               "invalid sort");
  vars1 = {b1, b11};
  vars = {vars1.data(), vars2.data()};
  terms = {v1, v4};
  ASSERT_DEATH(cvc5_define_funs_rec(d_solver,
                                    funs.size(),
                                    funs.data(),
                                    nvars.data(),
                                    vars.data(),
                                    terms.data(),
                                    false),
               "invalid sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  Cvc5Sort uninterpreted2 = cvc5_mk_uninterpreted_sort(tm, "u");
  Cvc5Sort bv_sort2 = cvc5_mk_bv_sort(tm, 32);

  domain = {bv_sort2, bv_sort2};
  Cvc5Sort fun_sort12 =
      cvc5_mk_fun_sort(tm, domain.size(), domain.data(), bv_sort2);
  domain = {uninterpreted2};
  Cvc5Sort fun_sort22 = cvc5_mk_fun_sort(
      tm, domain.size(), domain.data(), cvc5_get_integer_sort(tm));

  Cvc5Term b12 = cvc5_mk_var(tm, bv_sort2, "b1");
  Cvc5Term b112 = cvc5_mk_var(tm, bv_sort2, "b1");
  Cvc5Term b42 = cvc5_mk_var(tm, uninterpreted2, "b4");
  Cvc5Term v12 = cvc5_mk_const(tm, bv_sort2, "v1");
  Cvc5Term v22 = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "v2");
  Cvc5Term f12 = cvc5_mk_const(tm, fun_sort12, "f1");
  Cvc5Term f22 = cvc5_mk_const(tm, fun_sort22, "f2");

  funs = {f12, f22};
  nvars = {2, 1};
  vars1 = {b12, b112};
  vars2 = {b42};
  vars = {vars1.data(), vars2.data()};
  terms = {v12, v22};
  cvc5_define_funs_rec(slv,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  funs = {f1, f22};
  cvc5_define_funs_rec(slv,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  funs = {f12, f22};
  vars1 = {b1, b112};
  vars = {vars1.data(), vars2.data()};
  cvc5_define_funs_rec(slv,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  vars1 = {b12, b11};
  vars = {vars1.data(), vars2.data()};
  cvc5_define_funs_rec(slv,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  vars2 = {b42};
  vars = {vars1.data(), vars2.data()};
  terms = {v1, v22};
  cvc5_define_funs_rec(slv,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  terms = {v12, v2};
  cvc5_define_funs_rec(slv,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       false);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, define_funs_rec_wrong_logic)
{
  cvc5_set_logic(d_solver, "QF_BV");
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 32);
  std::vector<Cvc5Sort> domain = {bv_sort, bv_sort};
  Cvc5Sort fun_sort1 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), bv_sort);
  domain = {d_uninterpreted};
  Cvc5Sort fun_sort2 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  Cvc5Term b = cvc5_mk_var(d_tm, bv_sort, "b");
  Cvc5Term u = cvc5_mk_var(d_tm, d_uninterpreted, "u");
  Cvc5Term v1 = cvc5_mk_const(d_tm, bv_sort, "v1");
  Cvc5Term v2 = cvc5_mk_const(d_tm, d_int, "v2");
  Cvc5Term f1 = cvc5_mk_const(d_tm, fun_sort1, "f1");
  Cvc5Term f2 = cvc5_mk_const(d_tm, fun_sort2, "f2");

  std::vector<Cvc5Term> funs = {f1, f2};
  std::vector<size_t> nvars = {2, 1};
  std::vector<Cvc5Term> vars1 = {b, b};
  std::vector<Cvc5Term> vars2 = {u};
  std::vector<const Cvc5Term*> vars = {vars1.data(), vars2.data()};
  std::vector<Cvc5Term> terms = {v1, v2};

  ASSERT_DEATH(cvc5_define_funs_rec(d_solver,
                                    funs.size(),
                                    funs.data(),
                                    nvars.data(),
                                    vars.data(),
                                    terms.data(),
                                    false),
               "require a logic with quantifiers");
}

TEST_F(TestCApiBlackSolver, define_funs_rec_global)
{
  std::vector<Cvc5Sort> domain = {d_bool};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);
  cvc5_push(d_solver, 1);

  Cvc5Term btrue = cvc5_mk_true(d_tm);
  Cvc5Term b = cvc5_mk_var(d_tm, d_bool, "b");
  Cvc5Term g = cvc5_mk_const(d_tm, fun_sort, "g");
  // (define-funs-rec ((g ((b Bool)) Bool)) (b))
  std::vector<Cvc5Term> funs = {g};
  std::vector<size_t> nvars = {1};
  std::vector<Cvc5Term> vars1 = {b};
  std::vector<const Cvc5Term*> vars = {vars1.data()};
  std::vector<Cvc5Term> terms = {b};

  cvc5_define_funs_rec(d_solver,
                       funs.size(),
                       funs.data(),
                       nvars.data(),
                       vars.data(),
                       terms.data(),
                       true);

  // (assert (not (g true)))
  std::vector<Cvc5Term> args = {g, btrue};
  Cvc5Term t = cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {t};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));
  cvc5_pop(d_solver, 1);
  // (assert (not (g true)))
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()));
  res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));
}

TEST_F(TestCApiBlackSolver, get_assertions)
{
  Cvc5Term a = cvc5_mk_const(d_tm, d_bool, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, d_bool, "b");
  cvc5_assert_formula(d_solver, a);
  cvc5_assert_formula(d_solver, b);
  size_t size;
  auto res = cvc5_get_assertions(d_solver, &size);
  ASSERT_EQ(size, 2);
  ASSERT_TRUE(cvc5_term_is_equal(a, res[0]));
  ASSERT_TRUE(cvc5_term_is_equal(b, res[1]));
  ASSERT_DEATH(cvc5_get_assertions(nullptr, &size), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_assertions(d_solver, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_info)
{
  ASSERT_EQ(cvc5_get_info(d_solver, "name"), std::string("\"cvc5\""));
  ASSERT_DEATH(cvc5_get_info(d_solver, "asdf"), "unrecognized flag");
  ASSERT_DEATH(cvc5_get_info(nullptr, "name"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_info(d_solver, nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_option)
{
  ASSERT_EQ(cvc5_get_option(d_solver, "incremental"), std::string("true"));
  ASSERT_DEATH(cvc5_get_option(d_solver, "asdf"), "Unrecognized option");
  ASSERT_DEATH(cvc5_get_option(nullptr, "incremental"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_option(d_solver, nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_option_names)
{
  size_t size;
  auto names = cvc5_get_option_names(d_solver, &size);
  ASSERT_TRUE(size > 100);
  bool found_verbose = false;
  bool found_foobar = false;
  for (size_t i = 0; i < size; ++i)
  {
    if (names[i] == std::string("verbose"))
    {
      found_verbose = true;
    }
    else if (std::string(names[i]) == "foobar")
    {
      found_foobar = true;
    }
  }
  ASSERT_TRUE(found_verbose);
  ASSERT_FALSE(found_foobar);
  ASSERT_DEATH(cvc5_get_option_names(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_option_names(d_solver, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_option_info)
{
  Cvc5OptionInfo info;
  ASSERT_DEATH(cvc5_get_option_info(nullptr, "verbose", &info),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_option_info(d_solver, nullptr, &info),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_option_info(d_solver, "verbose", nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_option_info(d_solver, "asdf-invalid", &info),
               "Unrecognized option");

  cvc5_set_option(d_solver, "verbosity", "2");

  cvc5_get_option_info(d_solver, "verbose", &info);
  ASSERT_EQ(info.name, std::string("verbose"));
  ASSERT_EQ(info.num_aliases, 0);
  ASSERT_FALSE(info.is_regular);
  ASSERT_FALSE(info.is_expert);
  ASSERT_FALSE(info.is_set_by_user);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_VOID);
  ASSERT_EQ(cvc5_option_info_to_string(&info),
            std::string("OptionInfo{ verbose | void }"));

  // bool kind
  cvc5_get_option_info(d_solver, "print-success", &info);
  ASSERT_EQ(info.name, std::string("print-success"));
  ASSERT_EQ(info.num_aliases, 0);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_BOOL);
  ASSERT_FALSE(info.is_regular);
  ASSERT_FALSE(info.is_expert);
  ASSERT_FALSE(info.is_set_by_user);
  ASSERT_EQ(info.info_bool.dflt, false);
  ASSERT_EQ(info.info_bool.cur, false);
  ASSERT_EQ(cvc5_option_info_to_string(&info),
            std::string(
                "OptionInfo{ print-success | bool | false | default false }"));

  // int64 kind
  cvc5_get_option_info(d_solver, "verbosity", &info);
  ASSERT_EQ(info.name, std::string("verbosity"));
  ASSERT_EQ(info.num_aliases, 0);
  ASSERT_FALSE(info.is_regular);
  ASSERT_FALSE(info.is_expert);
  ASSERT_TRUE(info.is_set_by_user);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_INT64);
  ASSERT_EQ(info.info_int.dflt, 0);
  ASSERT_EQ(info.info_int.cur, 2);
  ASSERT_FALSE(info.info_int.has_min || info.info_int.has_max);
  ASSERT_EQ(
      cvc5_option_info_to_string(&info),
      std::string(
          "OptionInfo{ verbosity | set by user | int64_t | 2 | default 0 }"));

  // uint64 kind
  cvc5_get_option_info(d_solver, "rlimit", &info);
  ASSERT_EQ(info.name, std::string("rlimit"));
  ASSERT_EQ(info.num_aliases, 0);
  ASSERT_FALSE(info.is_regular);
  ASSERT_FALSE(info.is_expert);
  ASSERT_FALSE(info.is_set_by_user);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_UINT64);
  ASSERT_EQ(info.info_uint.dflt, 0);
  ASSERT_EQ(info.info_uint.cur, 0);
  ASSERT_FALSE(info.info_uint.has_min || info.info_uint.has_max);
  ASSERT_EQ(cvc5_option_info_to_string(&info),
            std::string("OptionInfo{ rlimit | uint64_t | 0 | default 0 }"));

  // double kind
  cvc5_get_option_info(d_solver, "random-freq", &info);
  ASSERT_EQ(info.name, std::string("random-freq"));
  ASSERT_EQ(info.num_aliases, 1);
  ASSERT_EQ(info.aliases[0], std::string("random-frequency"));
  ASSERT_FALSE(info.is_regular);
  ASSERT_TRUE(info.is_expert);
  ASSERT_FALSE(info.is_set_by_user);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_DOUBLE);
  ASSERT_EQ(info.info_double.dflt, 0.0);
  ASSERT_EQ(info.info_double.cur, 0.0);
  ASSERT_TRUE(info.info_double.has_min && info.info_double.has_max);
  ASSERT_EQ(info.info_double.min, 0.0);
  ASSERT_EQ(info.info_double.min, 0.0);
  ASSERT_EQ(cvc5_option_info_to_string(&info),
            std::string("OptionInfo{ random-freq, random-frequency | double | "
                        "0 | default 0 | 0 <= x <= 1 }"));

  // string kind
  cvc5_get_option_info(d_solver, "force-logic", &info);
  ASSERT_EQ(info.name, std::string("force-logic"));
  ASSERT_EQ(info.num_aliases, 0);
  ASSERT_FALSE(info.is_regular);
  ASSERT_FALSE(info.is_expert);
  ASSERT_FALSE(info.is_set_by_user);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_STR);
  ASSERT_EQ(info.info_str.dflt, std::string(""));
  ASSERT_EQ(info.info_str.cur, std::string(""));
  ASSERT_EQ(
      cvc5_option_info_to_string(&info),
      std::string("OptionInfo{ force-logic | string | \"\" | default \"\" }"));

  // mode option
  cvc5_get_option_info(d_solver, "simplification", &info);
  ASSERT_EQ(info.name, std::string("simplification"));
  ASSERT_EQ(info.num_aliases, 1);
  ASSERT_EQ(info.aliases[0], std::string("simplification-mode"));
  ASSERT_TRUE(info.is_regular);
  ASSERT_FALSE(info.is_expert);
  ASSERT_FALSE(info.is_set_by_user);
  ASSERT_EQ(info.kind, CVC5_OPTION_INFO_MODES);
  ASSERT_EQ(info.info_mode.dflt, std::string("batch"));
  ASSERT_EQ(info.info_mode.cur, std::string("batch"));
  ASSERT_EQ(info.info_mode.num_modes, 2);
  ASSERT_TRUE((info.info_mode.modes[0] == std::string("batch"))
              || (info.info_mode.modes[1] == std::string("batch")));
  ASSERT_TRUE((info.info_mode.modes[0] == std::string("none"))
              || (info.info_mode.modes[1] == std::string("none")));
  ASSERT_EQ(cvc5_option_info_to_string(&info),
            std::string("OptionInfo{ simplification, simplification-mode | "
                        "mode | batch | default batch | modes: batch, none }"));
}

TEST_F(TestCApiBlackSolver, get_unsat_assumptions1)
{
  cvc5_set_option(d_solver, "incremental", "false");
  std::vector<Cvc5Term> assumptions = {cvc5_mk_false(d_tm)};
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  size_t size;
  ASSERT_DEATH(cvc5_get_unsat_assumptions(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_unsat_assumptions(d_solver, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_unsat_assumptions(d_solver, &size),
               "cannot get unsat assumptions");
}

TEST_F(TestCApiBlackSolver, get_unsat_assumptions2)
{
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-unsat-assumptions", "false");
  std::vector<Cvc5Term> assumptions = {cvc5_mk_false(d_tm)};
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  size_t size;
  ASSERT_DEATH(cvc5_get_unsat_assumptions(d_solver, &size),
               "cannot get unsat assumptions");
}

TEST_F(TestCApiBlackSolver, get_unsat_assumptions3)
{
  cvc5_set_option(d_solver, "incremental", "true");
  cvc5_set_option(d_solver, "produce-unsat-assumptions", "true");
  std::vector<Cvc5Term> assumptions = {cvc5_mk_false(d_tm)};
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  size_t size;
  const Cvc5Term* res = cvc5_get_unsat_assumptions(d_solver, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res[0], cvc5_mk_false(d_tm)));
  assumptions = {cvc5_mk_true(d_tm)};
  cvc5_check_sat_assuming(d_solver, assumptions.size(), assumptions.data());
  ASSERT_DEATH(cvc5_get_unsat_assumptions(d_solver, &size),
               "cannot get unsat assumptions");
}

TEST_F(TestCApiBlackSolver, get_unsat_core0)
{
  cvc5_set_option(d_solver, "incremental", "true");
  cvc5_assert_formula(d_solver, cvc5_mk_false(d_tm));
  cvc5_check_sat(d_solver);
  size_t size;
  ASSERT_DEATH(cvc5_get_unsat_core(nullptr, &size), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_unsat_core(d_solver, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_unsat_core1)
{
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_assert_formula(d_solver, cvc5_mk_false(d_tm));
  cvc5_check_sat(d_solver);
  size_t size;
  ASSERT_DEATH(cvc5_get_unsat_core(d_solver, &size), "cannot get unsat core");
}

TEST_F(TestCApiBlackSolver, get_unsat_core2)
{
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-unsat-cores", "false");
  cvc5_assert_formula(d_solver, cvc5_mk_false(d_tm));
  cvc5_check_sat(d_solver);
  size_t size;
  ASSERT_DEATH(cvc5_get_unsat_core(d_solver, &size), "cannot get unsat core");
}

TEST_F(TestCApiBlackSolver, get_unsat_core_and_proof)
{
  cvc5_set_option(d_solver, "incremental", "true");
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");
  cvc5_set_option(d_solver, "produce-proofs", "true");

  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort u_to_int =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort int_pred =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  Cvc5Term f = cvc5_mk_const(d_tm, u_to_int, "f");
  Cvc5Term p = cvc5_mk_const(d_tm, int_pred, "p");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());

  args = {zero, f_x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {zero, f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {sum, one};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  cvc5_assert_formula(d_solver, p_0);
  args = {p_f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()));
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));

  size_t uc_size, proof_size;
  const Cvc5Term* uc = cvc5_get_unsat_core(d_solver, &uc_size);
  ASSERT_TRUE(uc_size > 0);

  (void)cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &proof_size);
  (void)cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_SAT, &proof_size);

  cvc5_reset_assertions(d_solver);
  for (size_t i = 0; i < uc_size; ++i)
  {
    cvc5_assert_formula(d_solver, uc[i]);
  }
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_unsat(res));
  (void)cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &proof_size);
}

TEST_F(TestCApiBlackSolver, get_unsat_core_lemmas1)
{
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");
  cvc5_set_option(d_solver, "unsat-cores-mode", "sat-proof");

  size_t size;
  // cannot ask before a check sat
  ASSERT_DEATH(cvc5_get_unsat_core_lemmas(d_solver, &size),
               "cannot get unsat core");

  cvc5_assert_formula(d_solver, cvc5_mk_false(d_tm));
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));
  (void)cvc5_get_unsat_core_lemmas(d_solver, &size);

  ASSERT_DEATH(cvc5_get_unsat_core_lemmas(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_unsat_core_lemmas(d_solver, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_unsat_core_lemmas2)
{
  cvc5_set_option(d_solver, "incremental", "true");
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");
  cvc5_set_option(d_solver, "produce-proofs", "true");

  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort u_to_int =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort int_pred =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  Cvc5Term f = cvc5_mk_const(d_tm, u_to_int, "f");
  Cvc5Term p = cvc5_mk_const(d_tm, int_pred, "p");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());

  args = {zero, f_x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {zero, f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {sum, one};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  cvc5_assert_formula(d_solver, p_0);
  args = {p_f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()));
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));

  size_t size;
  (void)cvc5_get_unsat_core_lemmas(d_solver, &size);
}

TEST_F(TestCApiBlackSolver, get_difficulty)
{
  cvc5_set_option(d_solver, "produce-difficulty", "true");
  size_t size;
  Cvc5Term *inputs, *values;
  ASSERT_DEATH(cvc5_get_difficulty(nullptr, &size, &inputs, &values),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_difficulty(d_solver, nullptr, &inputs, &values),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_difficulty(d_solver, &size, nullptr, &values),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_difficulty(d_solver, &size, &inputs, nullptr),
               "unexpected NULL argument");
  // cannot ask before a check sat
  ASSERT_DEATH(cvc5_get_difficulty(d_solver, &size, &inputs, &values),
               "cannot get difficulty");
  cvc5_check_sat(d_solver);
  cvc5_get_difficulty(d_solver, &size, &inputs, &values);
}

TEST_F(TestCApiBlackSolver, get_difficulty2)
{
  cvc5_check_sat(d_solver);
  size_t size;
  Cvc5Term *inputs, *values;
  // option is not set
  ASSERT_DEATH(cvc5_get_difficulty(d_solver, &size, &inputs, &values),
               "Cannot get difficulty");
}

TEST_F(TestCApiBlackSolver, get_difficulty3)
{
  cvc5_set_option(d_solver, "produce-difficulty", "true");
  size_t size;
  Cvc5Term *inputs, *values;
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term ten = cvc5_mk_integer_int64(d_tm, 10);
  std::vector<Cvc5Term> args = {x, ten};
  Cvc5Term f0 = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  args = {zero, x};
  Cvc5Term f1 = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  cvc5_assert_formula(d_solver, f0);
  cvc5_assert_formula(d_solver, f1);
  cvc5_check_sat(d_solver);
  cvc5_get_difficulty(d_solver, &size, &inputs, &values);
  ASSERT_EQ(size, 2);
  // difficulty should map assertions to integer values
  for (size_t i = 0; i < size; ++i)
  {
    ASSERT_TRUE(cvc5_term_is_equal(inputs[i], f0)
                || cvc5_term_is_equal(inputs[i], f1));
    ASSERT_EQ(cvc5_term_get_kind(values[i]), CVC5_KIND_CONST_INTEGER);
  }
}

TEST_F(TestCApiBlackSolver, get_timeout_core)
{
  cvc5_set_option(d_solver, "timeout-core-timeout", "100");
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");

  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term tt = cvc5_mk_true(d_tm);
  std::vector<Cvc5Term> args = {x, x};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_MULT, args.size(), args.data()),
          cvc5_mk_integer(d_tm, "501240912901901249014210220059591")};
  Cvc5Term hard = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  cvc5_assert_formula(d_solver, tt);
  cvc5_assert_formula(d_solver, hard);

  Cvc5Result result;
  size_t size;
  const Cvc5Term* core = cvc5_get_timeout_core(d_solver, &result, &size);
  ASSERT_TRUE(cvc5_result_is_unknown(result));
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(core[0], hard));

  ASSERT_DEATH(cvc5_get_timeout_core(nullptr, &result, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_timeout_core(d_solver, nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_timeout_core(d_solver, &result, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_timeout_core_unsat)
{
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");
  Cvc5Term ff = cvc5_mk_false(d_tm);
  Cvc5Term tt = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, tt);
  cvc5_assert_formula(d_solver, ff);
  cvc5_assert_formula(d_solver, tt);

  Cvc5Result result;
  size_t size;
  const Cvc5Term* core = cvc5_get_timeout_core(d_solver, &result, &size);
  ASSERT_TRUE(cvc5_result_is_unsat(result));
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(core[0], ff));
}

TEST_F(TestCApiBlackSolver, get_timeout_core_assuming)
{
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");
  Cvc5Term ff = cvc5_mk_false(d_tm);
  Cvc5Term tt = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, tt);

  std::vector<Cvc5Term> assumptions = {ff, tt};
  Cvc5Result result;
  size_t size;
  const Cvc5Term* core = cvc5_get_timeout_core_assuming(
      d_solver, assumptions.size(), assumptions.data(), &result, &size);
  ASSERT_TRUE(cvc5_result_is_unsat(result));
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(core[0], ff));
}

TEST_F(TestCApiBlackSolver, get_timeout_core_assuming_empty)
{
  cvc5_set_option(d_solver, "produce-unsat-cores", "true");
  std::vector<Cvc5Term> assumptions = {};
  Cvc5Result result;
  size_t size;
  ASSERT_DEATH(
      cvc5_get_timeout_core_assuming(
          d_solver, assumptions.size(), assumptions.data(), &result, &size),
      "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_proof_and_proof_to_string)
{
  cvc5_set_option(d_solver, "produce-proofs", "true");

  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort u_to_int =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort int_pred =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  Cvc5Term f = cvc5_mk_const(d_tm, u_to_int, "f");
  Cvc5Term p = cvc5_mk_const(d_tm, int_pred, "p");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());

  args = {zero, f_x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {zero, f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {sum, one};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  cvc5_assert_formula(d_solver, p_0);
  args = {p_f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()));
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));

  size_t size;
  ASSERT_DEATH(cvc5_get_proof(nullptr, CVC5_PROOF_COMPONENT_FULL, &size),
               "unexpected NULL");
  ASSERT_DEATH(cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, nullptr),
               "unexpected NULL");

  const Cvc5Proof* proofs =
      cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &size);
  ASSERT_TRUE(size > 0);

  std::string proof_str = cvc5_proof_to_string(
      d_solver, proofs[0], CVC5_PROOF_FORMAT_DEFAULT, 0, nullptr, nullptr);
  ASSERT_FALSE(proof_str.empty());
  proof_str = cvc5_proof_to_string(
      d_solver, proofs[0], CVC5_PROOF_FORMAT_ALETHE, 0, nullptr, nullptr);
  ASSERT_FALSE(proof_str.empty());
  proofs = cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_SAT, &size);
  proof_str = cvc5_proof_to_string(
      d_solver, proofs[0], CVC5_PROOF_FORMAT_NONE, 0, nullptr, nullptr);
  ASSERT_FALSE(proof_str.empty());
}

TEST_F(TestCApiBlackSolver, proof_to_string_assertion_names)
{
  cvc5_set_option(d_solver, "produce-proofs", "true");

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");

  std::vector<Cvc5Term> args = {x, y};
  Cvc5Term x_eq_y =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  args = {x_eq_y};
  Cvc5Term not_x_eq_y =
      cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());

  cvc5_assert_formula(d_solver, x_eq_y);
  cvc5_assert_formula(d_solver, not_x_eq_y);

  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));

  size_t size;
  const Cvc5Proof* proofs =
      cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &size);
  ASSERT_TRUE(size > 0);
  const Cvc5Term assertions[2] = {x_eq_y, not_x_eq_y};
  const char* names[2] = {"as1", "as2"};
  std::string proof_str = cvc5_proof_to_string(
      d_solver, proofs[0], CVC5_PROOF_FORMAT_ALETHE, 2, assertions, names);
  ASSERT_FALSE(proof_str.empty());
  ASSERT_LT(proof_str.find("as1"), std::string::npos);
  ASSERT_LT(proof_str.find("as2"), std::string::npos);
}

TEST_F(TestCApiBlackSolver, get_learned_literals)
{
  cvc5_set_option(d_solver, "produce-learned-literals", "true");

  size_t size;
  // cannot ask before a check sat
  ASSERT_DEATH(
      cvc5_get_learned_literals(d_solver, CVC5_LEARNED_LIT_TYPE_INPUT, &size),
      "cannot get learned literals");

  cvc5_check_sat(d_solver);
  (void)cvc5_get_learned_literals(d_solver, CVC5_LEARNED_LIT_TYPE_INPUT, &size);
  (void)cvc5_get_learned_literals(
      d_solver, CVC5_LEARNED_LIT_TYPE_PREPROCESS, &size);

  ASSERT_DEATH(
      cvc5_get_learned_literals(nullptr, CVC5_LEARNED_LIT_TYPE_INPUT, &size),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_get_learned_literals(d_solver, CVC5_LEARNED_LIT_TYPE_INPUT, nullptr),
      "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_learned_literals2)
{
  cvc5_set_option(d_solver, "produce-learned-literals", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term ten = cvc5_mk_integer_int64(d_tm, 10);
  std::vector<Cvc5Term> args = {x, ten};
  Cvc5Term f0 = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  args = {zero, x};
  Cvc5Term args1 = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  args = {y, zero};
  Cvc5Term args2 = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  args = {args1, args2};
  Cvc5Term f1 = cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data());
  cvc5_assert_formula(d_solver, f0);
  cvc5_assert_formula(d_solver, f1);
  cvc5_check_sat(d_solver);
  size_t size;
  (void)cvc5_get_learned_literals(d_solver, CVC5_LEARNED_LIT_TYPE_INPUT, &size);
}

TEST_F(TestCApiBlackSolver, get_value1)
{
  cvc5_set_option(d_solver, "produce-models", "false");
  Cvc5Term t = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, t);
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_get_value(d_solver, t), "cannot get value");
}

TEST_F(TestCApiBlackSolver, get_value2)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_false(d_tm);
  cvc5_assert_formula(d_solver, t);
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_get_value(d_solver, t), "cannot get value");
}

TEST_F(TestCApiBlackSolver, get_value3)
{
  cvc5_set_option(d_solver, "produce-models", "true");

  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort u_to_int =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort int_pred =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  Cvc5Term z = cvc5_mk_const(d_tm, d_uninterpreted, "z");
  Cvc5Term f = cvc5_mk_const(d_tm, u_to_int, "f");
  Cvc5Term p = cvc5_mk_const(d_tm, int_pred, "p");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());

  args = {zero, f_x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data()));
  args = {zero, f_y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data()));
  args = {sum, one};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data()));
  args = {p_0};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()));
  cvc5_assert_formula(d_solver, p_f_y);
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));

  (void)cvc5_get_value(d_solver, x);
  (void)cvc5_get_value(d_solver, y);
  (void)cvc5_get_value(d_solver, z);
  (void)cvc5_get_value(d_solver, sum);
  (void)cvc5_get_value(d_solver, p_f_y);

  ASSERT_DEATH(cvc5_get_value(nullptr, x), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_value(d_solver, nullptr), "invalid term");

  std::vector<Cvc5Term> a = {cvc5_get_value(d_solver, x),
                             cvc5_get_value(d_solver, y),
                             cvc5_get_value(d_solver, z)};
  size_t size;
  std::vector<Cvc5Term> terms = {x, y, z};
  const Cvc5Term* b =
      cvc5_get_values(d_solver, terms.size(), terms.data(), &size);
  ASSERT_EQ(size, 3);
  ASSERT_TRUE(cvc5_term_is_equal(a[0], b[0]));
  ASSERT_TRUE(cvc5_term_is_equal(a[1], b[1]));
  ASSERT_DEATH(cvc5_get_values(nullptr, terms.size(), terms.data(), &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_values(d_solver, terms.size(), nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_values(d_solver, terms.size(), terms.data(), nullptr),
               "unexpected NULL argument");

  Cvc5* slv = cvc5_new(d_tm);
  ASSERT_DEATH(cvc5_get_value(slv, x), "cannot get value");
  cvc5_delete(slv);

  slv = cvc5_new(d_tm);
  cvc5_set_option(slv, "produce-models", "true");
  ASSERT_DEATH(cvc5_get_value(slv, x), "cannot get value");
  cvc5_delete(slv);

  slv = cvc5_new(d_tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_check_sat(slv);
  (void)cvc5_get_value(slv, x);
  cvc5_delete(slv);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_check_sat(slv);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_get_value(slv, x);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_modelDomain_elements)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  Cvc5Term z = cvc5_mk_const(d_tm, d_uninterpreted, "z");
  std::vector<Cvc5Term> args = {x, y, z};
  Cvc5Term f = cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data());
  cvc5_assert_formula(d_solver, f);
  cvc5_check_sat(d_solver);
  size_t size;
  (void)cvc5_get_model_domain_elements(d_solver, d_uninterpreted, &size);
  ASSERT_TRUE(size >= 3);
  ASSERT_DEATH(cvc5_get_model_domain_elements(nullptr, d_uninterpreted, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_model_domain_elements(d_solver, nullptr, &size),
               "invalid sort");
  ASSERT_DEATH(
      cvc5_get_model_domain_elements(d_solver, d_uninterpreted, nullptr),
      "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_model_domain_elements(d_solver, d_int, &size),
               "expected an uninterpreted sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_check_sat(slv);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_get_model_domain_elements(slv, d_uninterpreted, &size);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, getModel_domain_elements2)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  cvc5_set_option(d_solver, "finite-model-find", "true");
  Cvc5Term x = cvc5_mk_var(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_var(d_tm, d_uninterpreted, "y");
  std::vector<Cvc5Term> args = {x, y};
  Cvc5Term eq = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  Cvc5Term bvl =
      cvc5_mk_term(d_tm, CVC5_KIND_VARIABLE_LIST, args.size(), args.data());
  args = {bvl, eq};
  Cvc5Term f = cvc5_mk_term(d_tm, CVC5_KIND_FORALL, args.size(), args.data());
  cvc5_assert_formula(d_solver, f);
  cvc5_check_sat(d_solver);
  size_t size;
  (void)cvc5_get_model_domain_elements(d_solver, d_uninterpreted, &size);
  // a model for the above must interpret u as size 1
  ASSERT_EQ(size, 1);
}

TEST_F(TestCApiBlackSolver, is_model_core_symbol)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  cvc5_set_option(d_solver, "model-cores", "simple");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  Cvc5Term z = cvc5_mk_const(d_tm, d_uninterpreted, "z");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  std::vector<Cvc5Term> args = {x, y};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data())};
  Cvc5Term f = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  cvc5_assert_formula(d_solver, f);
  cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_is_model_core_symbol(d_solver, x));
  ASSERT_TRUE(cvc5_is_model_core_symbol(d_solver, y));
  ASSERT_FALSE(cvc5_is_model_core_symbol(d_solver, z));

  ASSERT_DEATH(cvc5_is_model_core_symbol(nullptr, x),
               "unexpected NULL argument");
  ASSERT_FALSE(cvc5_is_model_core_symbol(d_solver, nullptr));
  ASSERT_DEATH(cvc5_is_model_core_symbol(d_solver, zero),
               "expected a free constant");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_check_sat(slv);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_is_model_core_symbol(slv, x);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_model)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  std::vector<Cvc5Term> args = {x, y};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data())};
  Cvc5Term f = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  cvc5_assert_formula(d_solver, f);
  cvc5_check_sat(d_solver);

  std::vector<Cvc5Sort> sorts = {d_uninterpreted};
  std::vector<Cvc5Term> terms = {x, y};
  (void)cvc5_get_model(
      d_solver, sorts.size(), sorts.data(), terms.size(), terms.data());

  ASSERT_DEATH(
      cvc5_get_model(
          nullptr, sorts.size(), sorts.data(), terms.size(), terms.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_model(
                   d_solver, sorts.size(), nullptr, terms.size(), terms.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_model(
                   d_solver, sorts.size(), sorts.data(), terms.size(), nullptr),
               "unexpected NULL argument");
  terms.push_back(nullptr);
  ASSERT_DEATH(
      cvc5_get_model(
          d_solver, sorts.size(), sorts.data(), terms.size(), terms.data()),
      "");
}

TEST_F(TestCApiBlackSolver, get_model2)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  std::vector<Cvc5Sort> sorts;
  std::vector<Cvc5Term> terms;
  ASSERT_DEATH(
      cvc5_get_model(
          d_solver, sorts.size(), sorts.data(), terms.size(), terms.data()),
      "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_model3)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  std::vector<Cvc5Sort> sorts;
  std::vector<Cvc5Term> terms;
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(
      cvc5_get_model(
          d_solver, sorts.size(), sorts.data(), terms.size(), terms.data()),
      "unexpected NULL argument");
  sorts.push_back(d_int);
  ASSERT_DEATH(
      cvc5_get_model(
          d_solver, sorts.size(), sorts.data(), terms.size(), terms.data()),
      "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_quantifier_elimination)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x};
  Cvc5Term vlist =
      cvc5_mk_term(d_tm, CVC5_KIND_VARIABLE_LIST, args.size(), args.data());
  args = {x, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data())};
  Cvc5Term b = cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data());
  args = {vlist, b};
  Cvc5Term forall =
      cvc5_mk_term(d_tm, CVC5_KIND_FORALL, args.size(), args.data());

  ASSERT_DEATH(cvc5_get_quantifier_elimination(nullptr, forall),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_quantifier_elimination(d_solver, nullptr),
               "invalid term");
  ASSERT_DEATH(cvc5_get_quantifier_elimination(d_solver, cvc5_mk_false(d_tm)),
               "Expecting a quantified formula");
  (void)cvc5_get_quantifier_elimination(d_solver, forall);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_check_sat(slv);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_get_quantifier_elimination(slv, forall);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_quantifier_elimination_disjunct)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x};
  Cvc5Term vlist =
      cvc5_mk_term(d_tm, CVC5_KIND_VARIABLE_LIST, args.size(), args.data());
  args = {x, cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data())};
  Cvc5Term b = cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data());
  args = {vlist, b};
  Cvc5Term forall =
      cvc5_mk_term(d_tm, CVC5_KIND_FORALL, args.size(), args.data());

  ASSERT_DEATH(cvc5_get_quantifier_elimination_disjunct(nullptr, forall),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_quantifier_elimination_disjunct(d_solver, nullptr),
               "invalid term");
  ASSERT_DEATH(
      cvc5_get_quantifier_elimination_disjunct(d_solver, cvc5_mk_false(d_tm)),
      "Expecting a quantified formula");
  (void)cvc5_get_quantifier_elimination_disjunct(d_solver, forall);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_check_sat(slv);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_get_quantifier_elimination(slv, forall);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, declare_sep_heap)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_declare_sep_heap(d_solver, d_int, d_int);
  // cannot declare separation logic heap more than once
  ASSERT_DEATH(cvc5_declare_sep_heap(d_solver, d_int, d_int),
               "cannot declare heap types");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  // no logic set yet
  Cvc5* slv = cvc5_new(tm);
  ASSERT_DEATH(cvc5_declare_sep_heap(d_solver, d_int, d_int),
               "cannot declare heap types");
  cvc5_delete(slv);

  // this will throw when NodeManager is not a singleton anymore
  slv = cvc5_new(tm);
  cvc5_set_logic(slv, "ALL");
  cvc5_declare_sep_heap(slv, cvc5_get_integer_sort(tm), d_int);
  cvc5_delete(slv);
  slv = cvc5_new(tm);
  cvc5_set_logic(slv, "ALL");
  cvc5_declare_sep_heap(slv, d_int, cvc5_get_integer_sort(tm));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_value_sep_heap1)
{
  cvc5_set_logic(d_solver, "QF_BV");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, t);
  ASSERT_DEATH(cvc5_get_value_sep_heap(d_solver),
               "cannot obtain separation logic expressions");
}

TEST_F(TestCApiBlackSolver, get_value_sep_heap2)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "false");
  check_simple_separation_constraints();
  ASSERT_DEATH(cvc5_get_value_sep_heap(d_solver),
               "cannot get separation heap term");
}

TEST_F(TestCApiBlackSolver, get_value_sep_heap3)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_false(d_tm);
  cvc5_assert_formula(d_solver, t);
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_get_value_sep_heap(d_solver), "after SAT or UNKNOWN");
}

TEST_F(TestCApiBlackSolver, get_value_sep_heap4)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, t);
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_get_value_sep_heap(d_solver), "Failed to obtain heap/nil");
}

TEST_F(TestCApiBlackSolver, get_value_sep_heap5)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  check_simple_separation_constraints();
  (void)cvc5_get_value_sep_heap(d_solver);
}

TEST_F(TestCApiBlackSolver, get_value_sep_nil1)
{
  cvc5_set_logic(d_solver, "QF_BV");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, t);
  ASSERT_DEATH(cvc5_get_value_sep_nil(d_solver),
               "cannot obtain separation logic expressions");
}

TEST_F(TestCApiBlackSolver, get_value_sep_nil2)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "false");
  check_simple_separation_constraints();
  ASSERT_DEATH(cvc5_get_value_sep_nil(d_solver), "cannot get separation nil");
}

TEST_F(TestCApiBlackSolver, get_value_sep_nil3)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_false(d_tm);
  cvc5_assert_formula(d_solver, t);
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_get_value_sep_nil(d_solver), "after SAT or UNKNOWN");
}

TEST_F(TestCApiBlackSolver, get_value_sep_nil4)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term t = cvc5_mk_true(d_tm);
  cvc5_assert_formula(d_solver, t);
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_get_value_sep_nil(d_solver),
               "Failed to obtain heap/nil expressions");
}

TEST_F(TestCApiBlackSolver, get_value_sep_nil5)
{
  cvc5_set_logic(d_solver, "ALL");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "produce-models", "true");
  check_simple_separation_constraints();
  cvc5_get_value_sep_nil(d_solver);
}

TEST_F(TestCApiBlackSolver, push1)
{
  cvc5_set_option(d_solver, "incremental", "true");
  cvc5_push(d_solver, 1);
  ASSERT_DEATH(cvc5_set_option(d_solver, "incremental", "false"),
               "is already fully initialized");
  ASSERT_DEATH(cvc5_set_option(d_solver, "incremental", "true"),
               "is already fully initialized");
}

TEST_F(TestCApiBlackSolver, push2)
{
  cvc5_set_option(d_solver, "incremental", "false");
  ASSERT_DEATH(cvc5_push(d_solver, 1), "cannot push");
}

TEST_F(TestCApiBlackSolver, push3)
{
  cvc5_set_option(d_solver, "incremental", "false");
  ASSERT_DEATH(cvc5_push(nullptr, 1), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, pop1)
{
  cvc5_set_option(d_solver, "incremental", "false");
  ASSERT_DEATH(cvc5_pop(d_solver, 1), "cannot pop");
}

TEST_F(TestCApiBlackSolver, pop2)
{
  cvc5_set_option(d_solver, "incremental", "true");
  ASSERT_DEATH(cvc5_pop(d_solver, 1), "cannot pop");
}

TEST_F(TestCApiBlackSolver, pop3)
{
  cvc5_set_option(d_solver, "incremental", "true");
  cvc5_push(d_solver, 1);
  cvc5_pop(d_solver, 1);
  ASSERT_DEATH(cvc5_pop(d_solver, 1), "cannot pop");
}

TEST_F(TestCApiBlackSolver, pop4)
{
  cvc5_set_option(d_solver, "incremental", "false");
  ASSERT_DEATH(cvc5_pop(nullptr, 1), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, set_info)
{
  ASSERT_DEATH(cvc5_set_info(d_solver, "cvc5-lagic", "QF_BV"),
               "unrecognized keyword");
  ASSERT_DEATH(cvc5_set_info(d_solver, "cvc2-logic", "QF_BV"),
               "unrecognized keyword");
  ASSERT_DEATH(cvc5_set_info(d_solver, "cvc5-logic", "asdf"),
               "unrecognized keyword");

  ASSERT_DEATH(cvc5_set_info(nullptr, "source", "asdf"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_set_info(d_solver, nullptr, "asdf"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_set_info(d_solver, "source", nullptr),
               "unexpected NULL argument");

  cvc5_set_info(d_solver, "source", "asdf");
  cvc5_set_info(d_solver, "category", "asdf");
  cvc5_set_info(d_solver, "difficulty", "asdf");
  cvc5_set_info(d_solver, "filename", "asdf");
  cvc5_set_info(d_solver, "license", "asdf");
  cvc5_set_info(d_solver, "name", "asdf");
  cvc5_set_info(d_solver, "notes", "asdf");

  cvc5_set_info(d_solver, "smt-lib-version", "2");
  cvc5_set_info(d_solver, "smt-lib-version", "2.0");
  cvc5_set_info(d_solver, "smt-lib-version", "2.5");
  cvc5_set_info(d_solver, "smt-lib-version", "2.6");
  ASSERT_DEATH(cvc5_set_info(d_solver, "smt-lib-version", ".0"),
               "invalid argument");

  cvc5_set_info(d_solver, "status", "sat");
  cvc5_set_info(d_solver, "status", "unsat");
  cvc5_set_info(d_solver, "status", "unknown");
  ASSERT_DEATH(cvc5_set_info(d_solver, "status", "asdf"), "invalid argument");
}

TEST_F(TestCApiBlackSolver, set_logic)
{
  ASSERT_DEATH(cvc5_set_logic(nullptr, "AUFLIRA"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_set_logic(d_solver, nullptr), "unexpected NULL argument");

  cvc5_set_logic(d_solver, "AUFLIRA");

  ASSERT_DEATH(cvc5_set_logic(d_solver, "AF_BV"), "logic is already set");
  cvc5_assert_formula(d_solver, cvc5_mk_true(d_tm));
  ASSERT_DEATH(cvc5_set_logic(d_solver, "AUFLIRA"), "logic is already set");
}

TEST_F(TestCApiBlackSolver, is_logic_set)
{
  ASSERT_DEATH(cvc5_is_logic_set(nullptr), "unexpected NULL argument");
  ASSERT_FALSE(cvc5_is_logic_set(d_solver));
  cvc5_set_logic(d_solver, "QF_BV");
  ASSERT_TRUE(cvc5_is_logic_set(d_solver));
}

TEST_F(TestCApiBlackSolver, get_logic)
{
  ASSERT_DEATH(cvc5_get_logic(nullptr), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_logic(d_solver), "logic has not yet been set");
  cvc5_set_logic(d_solver, "QF_BV");
  ASSERT_EQ(cvc5_get_logic(d_solver), std::string("QF_BV"));
}

TEST_F(TestCApiBlackSolver, set_option)
{
  cvc5_set_option(d_solver, "bv-sat-solver", "minisat");
  ASSERT_DEATH(cvc5_set_option(d_solver, "bv-sat-solver", "1"),
               "unknown option");
  cvc5_assert_formula(d_solver, cvc5_mk_true(d_tm));
  ASSERT_DEATH(cvc5_set_option(d_solver, "bv-sat-solver", "minisat"),
               "fully initialized");
}

TEST_F(TestCApiBlackSolver, reset_assertions)
{
  ASSERT_DEATH(cvc5_set_option(nullptr, "incremental", "true"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_set_option(d_solver, nullptr, "true"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_set_option(d_solver, "incremental", nullptr),
               "unexpected NULL argument");

  cvc5_set_option(d_solver, "incremental", "true");

  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 4);
  Cvc5Term one = cvc5_mk_bv_uint64(d_tm, 4, 1);
  Cvc5Term x = cvc5_mk_const(d_tm, bv_sort, "x");
  std::vector<Cvc5Term> args = {x, one};
  Cvc5Term ule =
      cvc5_mk_term(d_tm, CVC5_KIND_BITVECTOR_ULE, args.size(), args.data());
  args = {one, x};
  Cvc5Term srem =
      cvc5_mk_term(d_tm, CVC5_KIND_BITVECTOR_SREM, args.size(), args.data());
  cvc5_push(d_solver, 4);
  args = {srem, one};
  Cvc5Term slt =
      cvc5_mk_term(d_tm, CVC5_KIND_BITVECTOR_SLT, args.size(), args.data());
  cvc5_reset_assertions(d_solver);
  args = {slt, ule};
  cvc5_check_sat_assuming(d_solver, args.size(), args.data());
}

TEST_F(TestCApiBlackSolver, declare_sygus_var)
{
  cvc5_set_option(d_solver, "sygus", "true");

  std::vector<Cvc5Sort> domain = {d_int};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  (void)cvc5_declare_sygus_var(d_solver, "", d_bool);
  (void)cvc5_declare_sygus_var(d_solver, "", fun_sort);
  (void)cvc5_declare_sygus_var(d_solver, "b", d_bool);

  ASSERT_DEATH(cvc5_declare_sygus_var(nullptr, "", d_bool),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_sygus_var(d_solver, nullptr, d_bool),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_sygus_var(d_solver, "", nullptr), "invalid sort");

  Cvc5* slv = cvc5_new(d_tm);
  ASSERT_DEATH(cvc5_declare_sygus_var(slv, "", d_bool), "cannot call");
  cvc5_delete(slv);

  Cvc5TermManager* tm = cvc5_term_manager_new();
  slv = cvc5_new(tm);
  cvc5_set_option(slv, "sygus", "true");
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_declare_sygus_var(slv, "", d_bool);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, mk_grammar)
{
  Cvc5Term bt = cvc5_mk_true(d_tm);
  Cvc5Term bv = cvc5_mk_var(d_tm, d_bool, "b");
  Cvc5Term iv = cvc5_mk_var(d_tm, d_int, "i");

  std::vector<Cvc5Term> bvars;
  std::vector<Cvc5Term> symbols = {iv};
  (void)cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  bvars = {bv};
  (void)cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  ASSERT_DEATH(
      cvc5_mk_grammar(
          nullptr, bvars.size(), bvars.data(), symbols.size(), symbols.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_mk_grammar(
          d_solver, bvars.size(), bvars.data(), symbols.size(), nullptr),
      "unexpected NULL argument");

  symbols = {nullptr};
  ASSERT_DEATH(
      cvc5_mk_grammar(
          d_solver, bvars.size(), bvars.data(), symbols.size(), nullptr),
      "unexpected NULL argument");
  bvars = {nullptr};
  symbols = {iv};
  ASSERT_DEATH(
      cvc5_mk_grammar(
          d_solver, bvars.size(), bvars.data(), symbols.size(), nullptr),
      "unexpected NULL argument");
  bvars = {};
  symbols = {bt};
  ASSERT_DEATH(
      cvc5_mk_grammar(
          d_solver, bvars.size(), bvars.data(), symbols.size(), nullptr),
      "unexpected NULL argument");
  bvars = {bt};
  symbols = {iv};
  ASSERT_DEATH(
      cvc5_mk_grammar(
          d_solver, bvars.size(), bvars.data(), symbols.size(), nullptr),
      "unexpected NULL argument");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  bvars = {};
  symbols = {iv};
  (void)cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  bvars = {bv};
  symbols = {cvc5_mk_var(tm, cvc5_get_integer_sort(tm), "")};
  (void)cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, synth_fun)
{
  cvc5_set_option(d_solver, "sygus", "true");

  Cvc5Term x = cvc5_mk_var(d_tm, d_bool, "");
  Cvc5Term start1 = cvc5_mk_var(d_tm, d_bool, "");
  Cvc5Term start2 = cvc5_mk_var(d_tm, d_int, "");

  std::vector<Cvc5Term> bvars{x};
  std::vector<Cvc5Term> symbols{start1};
  Cvc5Grammar g1 = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  (void)cvc5_synth_fun(d_solver, "", 0, nullptr, d_bool);
  (void)cvc5_synth_fun(d_solver, "f1", bvars.size(), bvars.data(), d_bool);
  ASSERT_DEATH(cvc5_synth_fun_with_grammar(
                   d_solver, "f2", bvars.size(), bvars.data(), d_bool, g1),
               "invalid grammar");

  cvc5_grammar_add_rule(g1, start1, cvc5_mk_false(d_tm));

  symbols = {start2};
  Cvc5Grammar g2 = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  cvc5_grammar_add_rule(g2, start2, cvc5_mk_integer_int64(d_tm, 0));

  cvc5_synth_fun_with_grammar(
      d_solver, "f2", bvars.size(), bvars.data(), d_bool, g1);
  ASSERT_DEATH(cvc5_synth_fun_with_grammar(
                   nullptr, "f2", bvars.size(), bvars.data(), d_bool, g1),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_synth_fun_with_grammar(
                   d_solver, "f2", bvars.size(), bvars.data(), nullptr, g1),
               "invalid sort");
  ASSERT_DEATH(cvc5_synth_fun_with_grammar(
                   d_solver, "f2", bvars.size(), bvars.data(), d_bool, nullptr),
               "invalid grammar");

  ASSERT_DEATH(cvc5_synth_fun_with_grammar(
                   d_solver, "f6", bvars.size(), bvars.data(), d_bool, g2),
               "invalid Start symbol");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  cvc5_synth_fun_with_grammar(
      d_solver, "f8", bvars.size(), bvars.data(), d_bool, g1);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, declare_pool)
{
  Cvc5Sort set_sort = cvc5_mk_set_sort(d_tm, d_int);
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  // declare a pool with initial value { 0, x, y }
  std::vector<Cvc5Term> args = {zero, x, y};
  Cvc5Term p =
      cvc5_declare_pool(d_solver, "p", d_int, args.size(), args.data());
  // pool should have the same sort
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(p), set_sort));

  ASSERT_DEATH(cvc5_declare_pool(nullptr, "p", d_int, args.size(), args.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_declare_pool(d_solver, nullptr, d_int, args.size(), args.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_declare_pool(d_solver, "p", nullptr, args.size(), args.data()),
      "invalid sort");

  // no init values is allowed
  (void)cvc5_declare_pool(d_solver, "p", d_int, 0, nullptr);

  args = {nullptr, x, y};
  ASSERT_DEATH(
      cvc5_declare_pool(d_solver, "p", d_int, args.size(), args.data()),
      "invalid term at index 0");
  args = {zero, nullptr, y};
  ASSERT_DEATH(
      cvc5_declare_pool(d_solver, "p", d_int, args.size(), args.data()),
      "invalid term at index 1");
  args = {zero, x, nullptr};
  ASSERT_DEATH(
      cvc5_declare_pool(d_solver, "p", d_int, args.size(), args.data()),
      "invalid term at index 2");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // this will throw when NodeManager is not a singleton anymore
  args = {zero, x, y};
  Cvc5Term zero2 = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term x2 = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "x");
  Cvc5Term y2 = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "y");
  std::vector<Cvc5Term> args2 = {zero2, x2, y2};
  (void)cvc5_declare_pool(slv, "p", d_int, args2.size(), args2.data());
  (void)cvc5_declare_pool(
      slv, "p", cvc5_get_integer_sort(tm), args.size(), args.data());
  args2 = {zero2, x, y2};
  (void)cvc5_declare_pool(
      slv, "p", cvc5_get_integer_sort(tm), args2.size(), args2.data());
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, declare_oracle_fun_unsat)
{
  cvc5_set_option(d_solver, "oracles", "true");
  // f is the function implementing (lambda ((x Int)) (+ x 1))
  std::vector<Cvc5Sort> sorts = {d_int};
  Cvc5Term f = cvc5_declare_oracle_fun(
      d_solver,
      "f",
      sorts.size(),
      sorts.data(),
      d_int,
      d_tm,
      [](size_t size, const Cvc5Term* input, void* state) {
        Cvc5TermManager* ctm = static_cast<Cvc5TermManager*>(state);
        if (cvc5_term_is_uint32_value(input[0]))
        {
          return cvc5_mk_integer_int64(
              ctm, cvc5_term_get_uint32_value(input[0]) + 1);
        }
        return cvc5_mk_integer_int64(ctm, 0);
      });

  Cvc5Term three = cvc5_mk_integer_int64(d_tm, 3);
  Cvc5Term five = cvc5_mk_integer_int64(d_tm, 5);
  std::vector<Cvc5Term> args = {f, three};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data()),
          five};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  // (f 3) = 5
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "oracles", "true");
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  // this will throw when NodeManager is not a singleton anymore
  std::vector<Cvc5Sort> sorts2 = {int_sort};
  (void)cvc5_declare_oracle_fun(
      slv,
      "f",
      sorts.size(),
      sorts.data(),
      int_sort,
      tm,
      [](size_t size, const Cvc5Term* input, void* state) {
        Cvc5TermManager* ctm = static_cast<Cvc5TermManager*>(state);
        if (cvc5_term_is_uint32_value(input[0]))
        {
          return cvc5_mk_integer_int64(
              ctm, cvc5_term_get_uint32_value(input[0]) + 1);
        }
        return cvc5_mk_integer_int64(ctm, 0);
      });
  (void)cvc5_declare_oracle_fun(
      slv,
      "f",
      sorts2.size(),
      sorts2.data(),
      d_int,
      tm,
      [](size_t size, const Cvc5Term* input, void* state) {
        Cvc5TermManager* ctm = static_cast<Cvc5TermManager*>(state);
        if (cvc5_term_is_uint32_value(input[0]))
        {
          return cvc5_mk_integer_int64(
              ctm, cvc5_term_get_uint32_value(input[0]) + 1);
        }
        return cvc5_mk_integer_int64(ctm, 0);
      });
  (void)cvc5_declare_oracle_fun(
      slv,
      "f",
      sorts2.size(),
      sorts2.data(),
      int_sort,
      d_tm,
      [](size_t size, const Cvc5Term* input, void* state) {
        Cvc5TermManager* ctm = static_cast<Cvc5TermManager*>(state);
        if (cvc5_term_is_uint32_value(input[0]))
        {
          return cvc5_mk_integer_int64(
              ctm, cvc5_term_get_uint32_value(input[0]) + 1);
        }
        return cvc5_mk_integer_int64(ctm, 0);
      });
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, declare_oracle_fun_sat)
{
  cvc5_set_option(d_solver, "oracles", "true");
  cvc5_set_option(d_solver, "produce-models", "true");
  // f is the function implementing (lambda ((x Int)) (% x 10))
  std::vector<Cvc5Sort> sorts = {d_int};
  Cvc5Term f = cvc5_declare_oracle_fun(
      d_solver,
      "f",
      sorts.size(),
      sorts.data(),
      d_int,
      d_tm,
      [](size_t size, const Cvc5Term* input, void* state) {
        Assert(size == 1);
        Cvc5TermManager* ctm = static_cast<Cvc5TermManager*>(state);
        if (cvc5_term_is_uint32_value(input[0]))
        {
          return cvc5_mk_integer_int64(
              ctm, cvc5_term_get_uint32_value(input[0]) % 10);
        }
        return cvc5_mk_integer_int64(ctm, 0);
      });
  Cvc5Term seven = cvc5_mk_integer_int64(d_tm, 7);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  std::vector<Cvc5Term> args = {x, cvc5_mk_integer_int64(d_tm, 0)};
  Cvc5Term lb = cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
  cvc5_assert_formula(d_solver, lb);
  args = {x, cvc5_mk_integer_int64(d_tm, 100)};
  Cvc5Term ub = cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data());
  cvc5_assert_formula(d_solver, ub);
  args = {f, x};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data()),
          seven};
  Cvc5Term eq = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  cvc5_assert_formula(d_solver, eq);
  // x >= 0 ^ x <= 100 ^ (f x) = 7
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
  Cvc5Term xval = cvc5_get_value(d_solver, x);
  ASSERT_TRUE(cvc5_term_is_uint32_value(xval));
  ASSERT_TRUE(cvc5_term_get_uint32_value(xval) % 10 == 7);
}

TEST_F(TestCApiBlackSolver, declare_oracle_fun_sat2)
{
  cvc5_set_option(d_solver, "oracles", "true");
  cvc5_set_option(d_solver, "produce-models", "true");
  // f is the function implementing (lambda ((x Int) (y Int)) (= x y))
  std::vector<Cvc5Sort> sorts = {d_int, d_int};
  Cvc5Term eq = cvc5_declare_oracle_fun(
      d_solver,
      "eq",
      sorts.size(),
      sorts.data(),
      d_bool,
      d_tm,
      [](size_t size, const Cvc5Term* input, void* state) {
        Assert(size == 2);
        return cvc5_mk_boolean(static_cast<Cvc5TermManager*>(state),
                               cvc5_term_is_equal(input[0], input[1]));
      });
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  std::vector<Cvc5Term> args = {eq, x, y};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data())};
  Cvc5Term neq = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  cvc5_assert_formula(d_solver, neq);
  // (not (eq x y))
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
  Cvc5Term xval = cvc5_get_value(d_solver, x);
  Cvc5Term yval = cvc5_get_value(d_solver, y);
  ASSERT_TRUE(cvc5_term_is_disequal(xval, yval));
}

TEST_F(TestCApiBlackSolver, declare_oracle_fun_error1)
{
  cvc5_set_option(d_solver, "oracles", "true");
  std::vector<Cvc5Sort> sorts = {d_int, d_int};
  ASSERT_DEATH(cvc5_declare_oracle_fun(
                   nullptr,
                   "eq",
                   sorts.size(),
                   sorts.data(),
                   d_bool,
                   d_tm,
                   [](size_t size, const Cvc5Term* input, void* state) {
                     Assert(size == 2);
                     return cvc5_mk_boolean(
                         static_cast<Cvc5TermManager*>(state),
                         cvc5_term_is_equal(input[0], input[1]));
                   }),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_oracle_fun(
                   d_solver,
                   nullptr,
                   sorts.size(),
                   sorts.data(),
                   d_bool,
                   d_tm,
                   [](size_t size, const Cvc5Term* input, void* state) {
                     Assert(size == 2);
                     return cvc5_mk_boolean(
                         static_cast<Cvc5TermManager*>(state),
                         cvc5_term_is_equal(input[0], input[1]));
                   }),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_oracle_fun(
                   d_solver,
                   "eq",
                   0,
                   nullptr,
                   d_bool,
                   d_tm,
                   [](size_t size, const Cvc5Term* input, void* state) {
                     Assert(size == 2);
                     return cvc5_mk_boolean(
                         static_cast<Cvc5TermManager*>(state),
                         cvc5_term_is_equal(input[0], input[1]));
                   }),
               "");
  ASSERT_DEATH(cvc5_declare_oracle_fun(
                   d_solver,
                   "eq",
                   sorts.size(),
                   sorts.data(),
                   nullptr,
                   d_tm,
                   [](size_t size, const Cvc5Term* input, void* state) {
                     Assert(size == 2);
                     return cvc5_mk_boolean(
                         static_cast<Cvc5TermManager*>(state),
                         cvc5_term_is_equal(input[0], input[1]));
                   }),
               "invalid sort");
  // this won't die when declaring the function, only when the actual oracle
  // fun is called
  (void)cvc5_declare_oracle_fun(
      d_solver,
      "eq",
      sorts.size(),
      sorts.data(),
      d_bool,
      nullptr,
      [](size_t size, const Cvc5Term* input, void* state) {
        Assert(size == 2);
        return cvc5_mk_boolean(static_cast<Cvc5TermManager*>(state),
                               cvc5_term_is_equal(input[0], input[1]));
      });
  ASSERT_DEATH(
      cvc5_declare_oracle_fun(
          d_solver, "eq", sorts.size(), sorts.data(), d_bool, d_tm, nullptr),
      "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, declare_oracle_fun_error2)
{
  std::vector<Cvc5Sort> sorts = {d_int};
  // cannot declare without option
  ASSERT_DEATH(cvc5_declare_oracle_fun(
                   d_solver,
                   "f",
                   sorts.size(),
                   sorts.data(),
                   d_int,
                   d_tm,
                   [](size_t size, const Cvc5Term* input, void* state) {
                     Assert(size == 2);
                     return cvc5_mk_integer_int64(
                         static_cast<Cvc5TermManager*>(state), 0);
                   }),
               "unless oracles is enabled");
}

TEST_F(TestCApiBlackSolver, get_interpolant)
{
  cvc5_set_logic(d_solver, "QF_LIA");
  cvc5_set_option(d_solver, "produce-interpolants", "true");
  cvc5_set_option(d_solver, "incremental", "false");

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  Cvc5Term z = cvc5_mk_const(d_tm, d_int, "z");

  // Assumptions for interpolation: x + y > 0 /\ x < 0
  std::vector<Cvc5Term> args = {x, y};
  Cvc5Term add = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {add, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {x, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data()));

  // Conjecture for interpolation: y + z > 0 \/ z < 0
  args = {y, z};
  add = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {add, zero};
  Cvc5Term gt = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  args = {z, zero};
  Cvc5Term lt = cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data());
  args = {gt, lt};
  Cvc5Term conj = cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data());

  // Call the interpolation api, while the resulting interpolant is the output
  Cvc5Term output = cvc5_get_interpolant(d_solver, conj);
  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(cvc5_sort_is_boolean(cvc5_term_get_sort(output)));

  ASSERT_DEATH(cvc5_get_interpolant(nullptr, conj), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_interpolant(d_solver, nullptr), "invalid term");

  // try with a grammar, a simple grammar admitting true
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g =
      cvc5_mk_grammar(d_solver, 0, nullptr, symbols.size(), symbols.data());

  args = {zero, zero};
  Cvc5Term conj2 =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  ASSERT_DEATH(cvc5_get_interpolant_with_grammar(d_solver, conj2, g),
               "invalid grammar, must have at least one rule");
  cvc5_grammar_add_rule(g, start, ttrue);

  // Call the interpolation api, while the resulting interpolant is the output
  Cvc5Term output2 = cvc5_get_interpolant_with_grammar(d_solver, conj2, g);
  // interpolant must be true
  ASSERT_TRUE(cvc5_term_is_equal(output2, ttrue));

  ASSERT_DEATH(cvc5_get_interpolant_with_grammar(nullptr, conj2, g),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_interpolant_with_grammar(d_solver, nullptr, g),
               "invalid term");
  ASSERT_DEATH(cvc5_get_interpolant_with_grammar(d_solver, conj2, nullptr),
               "invalid grammar");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-interpolants", "true");
  // this will throw when NodeManager is not a singleton anymore
  Cvc5Term zzero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term sstart = cvc5_mk_var(tm, cvc5_get_boolean_sort(tm), "start");
  std::vector<Cvc5Term> ssymbols = {sstart};
  Cvc5Grammar gg =
      cvc5_mk_grammar(slv, 0, nullptr, ssymbols.size(), ssymbols.data());
  cvc5_grammar_add_rule(gg, sstart, cvc5_mk_true(tm));
  std::vector<Cvc5Term> aargs = {zzero, zzero};
  Cvc5Term cconj2 =
      cvc5_mk_term(tm, CVC5_KIND_EQUAL, aargs.size(), aargs.data());
  (void)cvc5_get_interpolant_with_grammar(slv, cconj2, gg);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_get_interpolant(slv, conj2);
  (void)cvc5_get_interpolant_with_grammar(slv, conj2, gg);
  (void)cvc5_get_interpolant_with_grammar(slv, cconj2, g);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_interpolant_next)
{
  cvc5_set_logic(d_solver, "QF_LIA");
  cvc5_set_option(d_solver, "produce-interpolants", "true");
  cvc5_set_option(d_solver, "incremental", "true");

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  Cvc5Term z = cvc5_mk_const(d_tm, d_int, "z");

  // Assumptions for interpolation: x + y > 0 /\ x < 0
  std::vector<Cvc5Term> args = {x, y};
  Cvc5Term add = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {add, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  args = {x, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data()));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  args = {y, z};
  add = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {add, zero};
  Cvc5Term gt = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  args = {z, zero};
  Cvc5Term lt = cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data());
  args = {gt, lt};
  Cvc5Term conj = cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data());

  Cvc5Term output = cvc5_get_interpolant(d_solver, conj);
  Cvc5Term output2 = cvc5_get_interpolant_next(d_solver);

  ASSERT_DEATH(cvc5_get_interpolant(nullptr, conj), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_interpolant(d_solver, nullptr), "invalid term");

  ASSERT_DEATH(cvc5_get_interpolant_next(nullptr), "unexpected NULL argument");

  // We expect the next output to be distinct
  ASSERT_TRUE(cvc5_term_is_disequal(output, output2));
}

TEST_F(TestCApiBlackSolver, get_abduct)
{
  cvc5_set_logic(d_solver, "QF_LIA");
  cvc5_set_option(d_solver, "produce-abducts", "true");
  cvc5_set_option(d_solver, "incremental", "false");

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");

  // Assumptions for abduction: x > 0
  std::vector<Cvc5Term> args = {x, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  // Conjecture for abduction: y > 0
  args = {y, zero};
  Cvc5Term conj = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  // Call the abduction api, while the resulting abduct is the output
  Cvc5Term output = cvc5_get_abduct(d_solver, conj);
  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(cvc5_sort_is_boolean(cvc5_term_get_sort(output)));

  ASSERT_DEATH(cvc5_get_abduct(nullptr, conj), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_abduct(d_solver, nullptr), "invalid term");

  // try with a grammar, a simple grammar admitting true
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g =
      cvc5_mk_grammar(d_solver, 0, nullptr, symbols.size(), symbols.data());
  args = {x, zero};
  Cvc5Term conj2 = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  ASSERT_DEATH(cvc5_get_abduct_with_grammar(d_solver, conj2, g),
               "invalid grammar, must have at least one rule");
  cvc5_grammar_add_rule(g, start, ttrue);

  // Call the abduction api, while the resulting abduct is the output
  Cvc5Term output2 = cvc5_get_abduct_with_grammar(d_solver, conj2, g);
  // abduct must be true
  ASSERT_TRUE(cvc5_term_is_equal(output2, ttrue));

  ASSERT_DEATH(cvc5_get_abduct_with_grammar(nullptr, conj2, g),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_abduct_with_grammar(d_solver, nullptr, g),
               "invalid term");
  ASSERT_DEATH(cvc5_get_abduct_with_grammar(d_solver, conj2, nullptr),
               "invalid grammar");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-abducts", "true");
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  // this will throw when NodeManager is not a singleton anymore
  Cvc5Term zzero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term xx = cvc5_mk_const(tm, int_sort, "x");
  Cvc5Term yy = cvc5_mk_const(tm, int_sort, "y");
  Cvc5Term sstart = cvc5_mk_var(tm, cvc5_get_boolean_sort(tm), "start");
  args = {xx, yy};
  Cvc5Term add = cvc5_mk_term(tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {add, zzero};
  cvc5_assert_formula(slv,
                      cvc5_mk_term(tm, CVC5_KIND_GT, args.size(), args.data()));
  std::vector<Cvc5Term> ssymbols = {sstart};
  Cvc5Grammar gg =
      cvc5_mk_grammar(slv, 0, nullptr, ssymbols.size(), ssymbols.data());
  cvc5_grammar_add_rule(gg, sstart, cvc5_mk_true(tm));
  std::vector<Cvc5Term> aargs = {zzero, zzero};
  Cvc5Term cconj2 =
      cvc5_mk_term(tm, CVC5_KIND_EQUAL, aargs.size(), aargs.data());
  (void)cvc5_get_abduct_with_grammar(slv, cconj2, gg);
  // this will throw when NodeManager is not a singleton anymore
  (void)cvc5_get_abduct(slv, conj2);
  (void)cvc5_get_abduct_with_grammar(slv, conj2, gg);
  (void)cvc5_get_abduct_with_grammar(slv, cconj2, g);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_abduct2)
{
  cvc5_set_logic(d_solver, "QF_LIA");
  cvc5_set_option(d_solver, "incremental", "false");

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  // Assumptions for abduction: x > 0
  std::vector<Cvc5Term> args = {x, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  // Conjecture for abduction: y > 0
  args = {y, zero};
  Cvc5Term conj = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  // Fails due to option not set
  ASSERT_DEATH(cvc5_get_abduct(d_solver, conj), "unless abducts are enabled");
}

TEST_F(TestCApiBlackSolver, get_abduct_next)
{
  cvc5_set_logic(d_solver, "QF_LIA");
  cvc5_set_option(d_solver, "produce-abducts", "true");
  cvc5_set_option(d_solver, "incremental", "true");

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");

  // Assumptions for abduction: x > 0
  std::vector<Cvc5Term> args = {x, zero};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data()));
  // Conjecture for abduction: y > 0
  args = {y, zero};
  Cvc5Term conj = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  // Call the abduction api, while the resulting abduct is the output
  Cvc5Term output = cvc5_get_abduct(d_solver, conj);
  Cvc5Term output2 = cvc5_get_abduct_next(d_solver);

  ASSERT_DEATH(cvc5_get_abduct(nullptr, conj), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_abduct(d_solver, nullptr), "invalid term");

  ASSERT_DEATH(cvc5_get_abduct_next(nullptr), "unexpected NULL argument");

  // should produce a different output
  ASSERT_TRUE(cvc5_term_is_disequal(output, output2));
}

TEST_F(TestCApiBlackSolver, block_model1)
{
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(d_solver);
  ASSERT_DEATH(cvc5_block_model(d_solver, CVC5_BLOCK_MODELS_MODE_LITERALS),
               "cannot get value");
}

TEST_F(TestCApiBlackSolver, block_model2)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  ASSERT_DEATH(cvc5_block_model(d_solver, CVC5_BLOCK_MODELS_MODE_LITERALS),
               "after SAT or UNKNOWN");
}

TEST_F(TestCApiBlackSolver, block_model3)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(d_solver);
  cvc5_block_model(d_solver, CVC5_BLOCK_MODELS_MODE_LITERALS);
  ASSERT_DEATH(cvc5_block_model(nullptr, CVC5_BLOCK_MODELS_MODE_LITERALS),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, block_model_values1)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(d_solver);
  args = {cvc5_mk_true(d_tm)};
  cvc5_block_model_values(d_solver, args.size(), args.data());

  ASSERT_DEATH(cvc5_block_model_values(nullptr, args.size(), args.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_block_model_values(d_solver, 0, nullptr),
               "unexpected NULL argument");
  args = {nullptr};
  ASSERT_DEATH(cvc5_block_model_values(d_solver, args.size(), args.data()),
               "invalid term at index 0");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  cvc5_check_sat(slv);
  args = {cvc5_mk_true(d_tm)};
  // this will throw when NodeManager is not a singleton anymore
  cvc5_block_model_values(slv, args.size(), args.data());
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, block_model_values2)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(d_solver);
  args = {x};
  cvc5_block_model_values(d_solver, args.size(), args.data());
}

TEST_F(TestCApiBlackSolver, block_model_values3)
{
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(d_solver);
  args = {x};
  ASSERT_DEATH(cvc5_block_model_values(d_solver, args.size(), args.data()),
               "cannot get value");
}

TEST_F(TestCApiBlackSolver, block_model_values4)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  args = {x};
  ASSERT_DEATH(cvc5_block_model_values(d_solver, args.size(), args.data()),
               "SAT or UNKNOWN response");
}

TEST_F(TestCApiBlackSolver, block_model_values5)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_bool, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  cvc5_check_sat(d_solver);
  args = {x};
  cvc5_block_model_values(d_solver, args.size(), args.data());
}

TEST_F(TestCApiBlackSolver, get_instantiations)
{
  std::vector<Cvc5Sort> sorts = {d_int};
  Cvc5Term p =
      cvc5_declare_fun(d_solver, "p", sorts.size(), sorts.data(), d_bool, true);
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  std::vector<Cvc5Term> args = {x};
  Cvc5Term bvl =
      cvc5_mk_term(d_tm, CVC5_KIND_VARIABLE_LIST, args.size(), args.data());
  args = {p, x};
  Cvc5Term app =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  args = {bvl, app};
  Cvc5Term q = cvc5_mk_term(d_tm, CVC5_KIND_FORALL, args.size(), args.data());
  cvc5_assert_formula(d_solver, q);
  Cvc5Term five = cvc5_mk_integer_int64(d_tm, 5);
  args = {p, five};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data())};
  Cvc5Term app2 = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  cvc5_assert_formula(d_solver, app2);
  ASSERT_DEATH(cvc5_get_instantiations(d_solver),
               "after a UNSAT, SAT or UNKNOWN response");
  cvc5_check_sat(d_solver);
  cvc5_get_instantiations(d_solver);
  ASSERT_DEATH(cvc5_get_instantiations(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, add_sygus_constraint)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term tbool = cvc5_mk_true(d_tm);

  cvc5_add_sygus_constraint(d_solver, tbool);
  ASSERT_DEATH(cvc5_add_sygus_constraint(nullptr, tbool),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_add_sygus_constraint(d_solver, nullptr), "invalid term");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "sygus", "true");
  // this will throw when NodeManager is not a singleton anymore
  cvc5_add_sygus_constraint(d_solver, cvc5_mk_true(tm));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_sygus_constraints)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  Cvc5Term tfalse = cvc5_mk_false(d_tm);
  cvc5_add_sygus_constraint(d_solver, ttrue);
  cvc5_add_sygus_constraint(d_solver, tfalse);
  size_t size;
  const Cvc5Term* constraints = cvc5_get_sygus_constraints(d_solver, &size);
  ASSERT_TRUE(cvc5_term_is_equal(ttrue, constraints[0]));
  ASSERT_TRUE(cvc5_term_is_equal(tfalse, constraints[1]));
  ASSERT_DEATH(cvc5_get_sygus_constraints(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_sygus_constraints(d_solver, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, add_sygus_assume)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term tbool = cvc5_mk_false(d_tm);
  Cvc5Term tint = cvc5_mk_integer_int64(d_tm, 1);

  cvc5_add_sygus_assume(d_solver, tbool);
  ASSERT_DEATH(cvc5_add_sygus_assume(nullptr, tbool),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_add_sygus_assume(d_solver, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_add_sygus_assume(d_solver, tint), "invalid argument");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "sygus", "true");
  // this will throw when NodeManager is not a singleton anymore
  cvc5_add_sygus_assume(slv, tbool);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_sygus_assumptions)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  Cvc5Term tfalse = cvc5_mk_false(d_tm);
  cvc5_add_sygus_assume(d_solver, ttrue);
  cvc5_add_sygus_assume(d_solver, tfalse);
  cvc5_add_sygus_assume(d_solver, ttrue);
  cvc5_add_sygus_assume(d_solver, tfalse);
  size_t size;
  const Cvc5Term* assumptions = cvc5_get_sygus_assumptions(d_solver, &size);
  ASSERT_TRUE(cvc5_term_is_equal(ttrue, assumptions[0]));
  ASSERT_TRUE(cvc5_term_is_equal(tfalse, assumptions[1]));
  ASSERT_DEATH(cvc5_get_sygus_assumptions(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_sygus_assumptions(d_solver, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, add_sygus_inv_constraint)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term tint = cvc5_mk_integer_int64(d_tm, 1);

  std::vector<Cvc5Sort> domain = {d_real};
  Cvc5Term inv = cvc5_declare_fun(
      d_solver, "inv", domain.size(), domain.data(), d_bool, true);
  Cvc5Term pre = cvc5_declare_fun(
      d_solver, "pre", domain.size(), domain.data(), d_bool, true);
  domain = {d_real, d_real};
  Cvc5Term trans = cvc5_declare_fun(
      d_solver, "trans", domain.size(), domain.data(), d_bool, true);
  domain = {d_real};
  Cvc5Term post = cvc5_declare_fun(
      d_solver, "post", domain.size(), domain.data(), d_bool, true);

  Cvc5Term inv1 = cvc5_declare_fun(
      d_solver, "inv1", domain.size(), domain.data(), d_real, true);
  domain = {d_bool, d_real};
  Cvc5Term trans1 = cvc5_declare_fun(
      d_solver, "trans1", domain.size(), domain.data(), d_bool, true);
  domain = {d_real, d_bool};
  Cvc5Term trans2 = cvc5_declare_fun(
      d_solver, "trans2", domain.size(), domain.data(), d_bool, true);
  domain = {d_real, d_real};
  Cvc5Term trans3 = cvc5_declare_fun(
      d_solver, "trans3", domain.size(), domain.data(), d_real, true);

  cvc5_add_sygus_inv_constraint(d_solver, inv, pre, trans, post);

  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(nullptr, inv, pre, trans, post),
               "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_add_sygus_inv_constraint(d_solver, nullptr, pre, trans, post),
      "invalid term");
  ASSERT_DEATH(
      cvc5_add_sygus_inv_constraint(d_solver, inv, nullptr, trans, post),
      "invalid term");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, nullptr, post),
               "invalid term");
  ASSERT_DEATH(
      cvc5_add_sygus_inv_constraint(d_solver, inv, pre, trans, nullptr),
      "invalid term");

  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, tint, pre, trans, post),
               "invalid argument");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv1, pre, trans, post),
               "invalid argument");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, trans, trans, post),
               "have the same sort");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, tint, post),
               "expected the sort of trans");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, pre, post),
               "expected the sort of trans");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, trans1, post),
               "expected the sort of trans");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, trans2, post),
               "expected the sort of trans");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, trans3, post),
               "expected the sort of trans");
  ASSERT_DEATH(cvc5_add_sygus_inv_constraint(d_solver, inv, pre, trans, trans),
               "expected inv and post to have the same sort");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "sygus", "true");
  Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);
  Cvc5Sort real_sort = cvc5_get_real_sort(tm);
  std::vector<Cvc5Sort> domain2 = {real_sort};
  Cvc5Term inv22 = cvc5_declare_fun(
      slv, "inv", domain2.size(), domain2.data(), bool_sort, true);
  Cvc5Term pre22 = cvc5_declare_fun(
      slv, "pre", domain2.size(), domain2.data(), bool_sort, true);
  domain2 = {real_sort, real_sort};
  Cvc5Term trans22 = cvc5_declare_fun(
      slv, "trans", domain2.size(), domain2.data(), bool_sort, true);
  domain2 = {real_sort};
  Cvc5Term post22 = cvc5_declare_fun(
      slv, "post", domain2.size(), domain2.data(), bool_sort, true);
  cvc5_add_sygus_inv_constraint(slv, inv22, pre22, trans22, post22);
  // this will throw when NodeManager is not a singleton anymore
  cvc5_add_sygus_inv_constraint(slv, inv, pre22, trans22, post22);
  cvc5_add_sygus_inv_constraint(slv, inv22, pre, trans22, post22);
  cvc5_add_sygus_inv_constraint(slv, inv22, pre22, trans, post22);
  cvc5_add_sygus_inv_constraint(slv, inv22, pre22, trans22, post);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, check_synth)
{
  // requires option to be set
  ASSERT_DEATH(cvc5_check_synth(d_solver),
               "cannot check for a synthesis solution");
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_check_synth(d_solver);
  ASSERT_DEATH(cvc5_check_synth(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_synth_solution)
{
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_set_option(d_solver, "incremental", "false");

  Cvc5Term x = cvc5_mk_false(d_tm);
  Cvc5Term f = cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);

  ASSERT_DEATH(cvc5_get_synth_solution(d_solver, f), "not in a state");

  Cvc5SynthResult res = cvc5_check_synth(d_solver);
  ASSERT_TRUE(cvc5_synth_result_has_solution(res));

  cvc5_get_synth_solution(d_solver, f);
  cvc5_get_synth_solution(d_solver, f);

  ASSERT_DEATH(cvc5_get_synth_solution(nullptr, f), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_synth_solution(d_solver, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_get_synth_solution(d_solver, x),
               "synthesis solution not found for given term");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  ASSERT_DEATH(cvc5_get_synth_solution(slv, f), "not in a state");
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, get_synth_solutions)
{
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_set_option(d_solver, "incremental", "false");

  Cvc5Term x = cvc5_mk_false(d_tm);
  Cvc5Term f = cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);

  std::vector<Cvc5Term> args{f};
  ASSERT_DEATH(cvc5_get_synth_solutions(d_solver, args.size(), args.data()),
               "not in a state");

  cvc5_check_synth(d_solver);

  cvc5_get_synth_solutions(d_solver, args.size(), args.data());
  args = {f, f};
  cvc5_get_synth_solutions(d_solver, args.size(), args.data());

  ASSERT_DEATH(cvc5_get_synth_solutions(d_solver, 0, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_synth_solutions(nullptr, args.size(), args.data()),
               "unexpected NULL argument");
  args = {nullptr};
  ASSERT_DEATH(cvc5_get_synth_solutions(d_solver, args.size(), args.data()),
               "invalid term at index 0");
  args = {x};
  ASSERT_DEATH(cvc5_get_synth_solutions(d_solver, args.size(), args.data()),
               "synthesis solution not found for term at index 0");

  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  ASSERT_DEATH(cvc5_get_synth_solutions(slv, args.size(), args.data()),
               "not in a state");
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackSolver, check_synth_next)
{
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_set_option(d_solver, "incremental", "true");

  Cvc5Term f = cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);

  Cvc5SynthResult res = cvc5_check_synth(d_solver);
  ASSERT_TRUE(cvc5_synth_result_has_solution(res));

  std::vector<Cvc5Term> args{f};
  cvc5_get_synth_solutions(d_solver, args.size(), args.data());

  res = cvc5_check_synth_next(d_solver);
  ASSERT_TRUE(cvc5_synth_result_has_solution(res));
  cvc5_get_synth_solutions(d_solver, args.size(), args.data());

  ASSERT_DEATH(cvc5_check_synth_next(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, check_synth_next2)
{
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_set_option(d_solver, "incremental", "false");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  cvc5_check_synth(d_solver);
  ASSERT_DEATH(cvc5_check_synth_next(d_solver),
               "cannot check for a next synthesis solution");
}

TEST_F(TestCApiBlackSolver, check_synth_next3)
{
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_set_option(d_solver, "incremental", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  ASSERT_DEATH(cvc5_check_synth_next(d_solver), "unless immediately preceded");
}

TEST_F(TestCApiBlackSolver, find_synth)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g =
      cvc5_mk_grammar(d_solver, 0, nullptr, symbols.size(), symbols.data());

  ASSERT_DEATH(
      cvc5_synth_fun_with_grammar(d_solver, "f", 0, nullptr, d_bool, g),
      "invalid grammar");

  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  Cvc5Term tfalse = cvc5_mk_false(d_tm);
  cvc5_grammar_add_rule(g, start, ttrue);
  cvc5_grammar_add_rule(g, start, tfalse);
  (void)cvc5_synth_fun_with_grammar(d_solver, "f", 0, nullptr, d_bool, g);

  // should enumerate based on the grammar of the function to synthesize above
  Cvc5Term t = cvc5_find_synth(d_solver, CVC5_FIND_SYNTH_TARGET_ENUM);
  ASSERT_TRUE(t && cvc5_sort_is_boolean(cvc5_term_get_sort(t)));

  ASSERT_DEATH(cvc5_find_synth(nullptr, CVC5_FIND_SYNTH_TARGET_ENUM),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_find_synth(d_solver, static_cast<Cvc5FindSynthTarget>(125)),
               "invalid find synthesis target");

  ASSERT_DEATH(
      cvc5_find_synth_with_grammar(nullptr, CVC5_FIND_SYNTH_TARGET_ENUM, g),
      "unexpected NULL argument");
  ASSERT_DEATH(cvc5_find_synth_with_grammar(
                   d_solver, static_cast<Cvc5FindSynthTarget>(125), g),
               "invalid find synthesis target");
  ASSERT_DEATH(cvc5_find_synth_with_grammar(
                   d_solver, CVC5_FIND_SYNTH_TARGET_ENUM, nullptr),
               "invalid grammar");
}

TEST_F(TestCApiBlackSolver, find_synth2)
{
  cvc5_set_option(d_solver, "sygus", "true");
  cvc5_set_option(d_solver, "incremental", "true");

  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g =
      cvc5_mk_grammar(d_solver, 0, nullptr, symbols.size(), symbols.data());
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  Cvc5Term tfalse = cvc5_mk_false(d_tm);
  cvc5_grammar_add_rule(g, start, ttrue);
  cvc5_grammar_add_rule(g, start, tfalse);

  // should enumerate true/false
  Cvc5Term t =
      cvc5_find_synth_with_grammar(d_solver, CVC5_FIND_SYNTH_TARGET_ENUM, g);
  ASSERT_TRUE(t && cvc5_sort_is_boolean(cvc5_term_get_sort(t)));
  t = cvc5_find_synth_next(d_solver);
  ASSERT_TRUE(t && cvc5_sort_is_boolean(cvc5_term_get_sort(t)));

  ASSERT_DEATH(cvc5_find_synth_next(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSolver, get_statistics)
{
  ASSERT_DEATH(cvc5_get_statistics(nullptr), "unexpected NULL argument");

  // do some reasoning to make sure we have statistics
  {
    Cvc5Sort s2 = cvc5_mk_array_sort(d_tm, d_int, d_int);
    Cvc5Term t1 = cvc5_mk_const(d_tm, d_int, "i");
    Cvc5Term t2 = cvc5_mk_const(d_tm, s2, "a");
    std::vector<Cvc5Term> args = {t2, t1};
    args = {cvc5_mk_term(d_tm, CVC5_KIND_SELECT, args.size(), args.data()), t1};
    cvc5_assert_formula(
        d_solver,
        cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data()));
    cvc5_check_sat(d_solver);
  }
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  (void)cvc5_stats_to_string(stats);

  Cvc5Stat stat1 = cvc5_stats_get(stats, "global::totalTime");
  ASSERT_FALSE(cvc5_stat_is_internal(stat1));
  ASSERT_FALSE(cvc5_stat_is_default(stat1));
  ASSERT_TRUE(cvc5_stat_is_string(stat1));
  (void)cvc5_stat_to_string(stat1);

  std::string time = cvc5_stat_get_string(stat1);
  ASSERT_TRUE(time.rfind("ms") == time.size() - 2);  // ends with "ms"
  ASSERT_FALSE(cvc5_stat_is_double(stat1));

  Cvc5Stat stat2 = cvc5_stats_get(stats, "resource::resourceUnitsUsed");
  ASSERT_TRUE(cvc5_stat_is_internal(stat2));
  ASSERT_FALSE(cvc5_stat_is_default(stat2));
  ASSERT_TRUE(cvc5_stat_is_int(stat2));
  ASSERT_TRUE(cvc5_stat_get_int(stat2) >= 0);
  (void)cvc5_stat_to_string(stat2);

  cvc5_stats_iter_init(stats, true, true);
  bool hasstats = false;
  while (cvc5_stats_iter_has_next(stats))
  {
    hasstats = true;
    const char* name;
    Cvc5Stat stat = cvc5_stats_iter_next(stats, &name);
    (void)cvc5_stat_to_string(stat);
    if (name == std::string("theory::arrays::avgIndexListLength"))
    {
      ASSERT_TRUE(cvc5_stat_is_internal(stat));
      ASSERT_TRUE(cvc5_stat_is_double(stat));
      ASSERT_TRUE(std::isnan(cvc5_stat_get_double(stat)));
    }
  }
  ASSERT_TRUE(hasstats);
}

TEST_F(TestCApiBlackSolver, print_statistics_safe)
{
  testing::internal::CaptureStdout();
  cvc5_print_stats_safe(d_solver, STDOUT_FILENO);
  testing::internal::GetCapturedStdout();
}

namespace {
const Cvc5Term* plugin_unsat_check(size_t* size, void* state)
{
  static thread_local std::vector<Cvc5Term> lemmas;
  // add the "false" lemma.
  Cvc5Term flem = cvc5_mk_false(static_cast<Cvc5TermManager*>(state));
  lemmas = {flem};
  *size = lemmas.size();
  return lemmas.data();
}
const char* plugin_unsat_get_name() { return "PluginUnsat"; }
}  // namespace

TEST_F(TestCApiBlackSolver, plugin_unsat)
{
  Cvc5Plugin plugin{&plugin_unsat_check,
                    nullptr,
                    nullptr,
                    &plugin_unsat_get_name,
                    d_tm,
                    nullptr,
                    nullptr};
  cvc5_add_plugin(d_solver, &plugin);
  ASSERT_TRUE(plugin.get_name() == std::string("PluginUnsat"));
  // should be unsat since the plugin above asserts "false" as a lemma
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));
}

namespace {
void plugin_listen_notify_sat_clause(const Cvc5Term clause, void* state)
{
  *static_cast<bool*>(state) = true;
}
void plugin_listen_notify_theory_lemma(const Cvc5Term lemma, void* state)
{
  *static_cast<bool*>(state) = true;
}
const char* plugin_listen_get_name() { return "PluginListen"; }
}  // namespace

TEST_F(TestCApiBlackSolver, plugin_listen)
{
  bool clause_seen, lemma_seen;
  Cvc5Plugin plugin{nullptr,
                    &plugin_listen_notify_sat_clause,
                    &plugin_listen_notify_theory_lemma,
                    &plugin_listen_get_name,
                    nullptr,
                    &clause_seen,
                    &lemma_seen};

  // NOTE: this shouldn't be necessary but ensures notify_sat_clause is called
  // here.
  cvc5_set_option(d_solver, "plugin-notify-sat-clause-in-solve", "false");
  cvc5_add_plugin(d_solver, &plugin);
  Cvc5Sort string_sort = cvc5_get_string_sort(d_tm);
  Cvc5Term x = cvc5_mk_const(d_tm, string_sort, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, string_sort, "y");
  std::vector<Cvc5Term> args{x, y};
  Cvc5Term ctn1 =
      cvc5_mk_term(d_tm, CVC5_KIND_STRING_CONTAINS, args.size(), args.data());
  args = {y, x};
  Cvc5Term ctn2 =
      cvc5_mk_term(d_tm, CVC5_KIND_STRING_CONTAINS, args.size(), args.data());
  args = {ctn1, ctn2};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  args = {x};
  Cvc5Term lx =
      cvc5_mk_term(d_tm, CVC5_KIND_STRING_LENGTH, args.size(), args.data());
  args = {y};
  Cvc5Term ly =
      cvc5_mk_term(d_tm, CVC5_KIND_STRING_LENGTH, args.size(), args.data());
  args = {lx, ly};
  Cvc5Term lc = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  cvc5_assert_formula(d_solver, lc);
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
  // above input formulas should induce a theory lemma and SAT clause learning
  ASSERT_TRUE(lemma_seen);
  ASSERT_TRUE(clause_seen);
}

TEST_F(TestCApiBlackSolver, tuple_project)
{
  std::vector<Cvc5Term> args = {cvc5_mk_string(d_tm, "Z", false)};
  std::vector<Cvc5Term> elements = {
      cvc5_mk_true(d_tm),
      cvc5_mk_integer_int64(d_tm, 3),
      cvc5_mk_string(d_tm, "C", false),
      cvc5_mk_term(d_tm, CVC5_KIND_SET_SINGLETON, args.size(), args.data())};

  Cvc5Term tuple = cvc5_mk_tuple(d_tm, elements.size(), elements.data());

  std::vector<uint32_t> indices1 = {};
  std::vector<uint32_t> indices2 = {0};
  std::vector<uint32_t> indices3 = {0, 1};
  std::vector<uint32_t> indices4 = {0, 0, 2, 2, 3, 3, 0};
  std::vector<uint32_t> indices5 = {4};
  std::vector<uint32_t> indices6 = {0, 4};

  args = {tuple};
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(
          d_tm, CVC5_KIND_TUPLE_PROJECT, indices1.size(), indices1.data()),
      args.size(),
      args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(
          d_tm, CVC5_KIND_TUPLE_PROJECT, indices2.size(), indices2.data()),
      args.size(),
      args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(
          d_tm, CVC5_KIND_TUPLE_PROJECT, indices3.size(), indices3.data()),
      args.size(),
      args.data());
  (void)cvc5_mk_term_from_op(
      d_tm,
      cvc5_mk_op(
          d_tm, CVC5_KIND_TUPLE_PROJECT, indices4.size(), indices4.data()),
      args.size(),
      args.data());

  ASSERT_DEATH(
      cvc5_mk_term_from_op(
          d_tm,
          cvc5_mk_op(
              d_tm, CVC5_KIND_TUPLE_PROJECT, indices5.size(), indices5.data()),
          args.size(),
          args.data()),
      "Project index 4");
  ASSERT_DEATH(
      cvc5_mk_term_from_op(
          d_tm,
          cvc5_mk_op(
              d_tm, CVC5_KIND_TUPLE_PROJECT, indices6.size(), indices6.data()),
          args.size(),
          args.data()),
      "Project index 4");

  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};

  Cvc5Op op =
      cvc5_mk_op(d_tm, CVC5_KIND_TUPLE_PROJECT, indices.size(), indices.data());
  Cvc5Term projection =
      cvc5_mk_term_from_op(d_tm, op, args.size(), args.data());

  Cvc5Datatype datatype = cvc5_sort_get_datatype(cvc5_term_get_sort(tuple));
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(datatype, 0);

  for (size_t i = 0; i < indices.size(); i++)
  {
    args = {cvc5_dt_sel_get_term(cvc5_dt_cons_get_selector(cons, indices[i])),
            tuple};
    Cvc5Term selected =
        cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, args.size(), args.data());
    Cvc5Term simplified = cvc5_simplify(d_solver, selected, false);
    ASSERT_TRUE(cvc5_term_is_equal(elements[indices[i]], simplified));
  }

  ASSERT_EQ(
      std::string(
          "((_ tuple.project 0 3 2 0 1 2) (tuple true 3 \"C\" (set.singleton "
          "\"Z\")))"),
      cvc5_term_to_string(projection));
}

TEST_F(TestCApiBlackSolver, vertical_bars)
{
  Cvc5Term a = cvc5_declare_fun(d_solver, "|a |", 0, nullptr, d_real, true);
  ASSERT_EQ(std::string("|a |"), cvc5_term_to_string(a));
}

TEST_F(TestCApiBlackSolver, get_version)
{
  std::cout << cvc5_get_version(d_solver) << std::endl;
}

TEST_F(TestCApiBlackSolver, multiple_solvers)
{
  Cvc5Term zero, value1, value2;
  Cvc5Term deffun;
  {
    Cvc5* s1 = cvc5_new(d_tm);
    cvc5_set_logic(s1, "ALL");
    cvc5_set_option(s1, "produce-models", "true");
    Cvc5Term fun1 = cvc5_declare_fun(s1, "f1", 0, nullptr, d_int, true);
    Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
    zero = cvc5_mk_integer_int64(d_tm, 0);
    std::vector<Cvc5Term> args = {x};
    deffun =
        cvc5_define_fun(s1, "f", args.size(), args.data(), d_int, zero, true);
    args = {fun1, zero};
    cvc5_assert_formula(
        s1, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
    cvc5_check_sat(s1);
    value1 = cvc5_get_value(s1, fun1);
    cvc5_delete(s1);
  }
  ASSERT_TRUE(cvc5_term_is_equal(zero, value1));
  {
    Cvc5* s2 = cvc5_new(d_tm);
    cvc5_set_logic(s2, "ALL");
    cvc5_set_option(s2, "produce-models", "true");
    Cvc5Term fun2 = cvc5_declare_fun(s2, "f2", 0, nullptr, d_int, true);
    std::vector<Cvc5Term> args = {fun2, value1};
    cvc5_assert_formula(
        s2, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
    cvc5_check_sat(s2);
    value2 = cvc5_get_value(s2, fun2);
    cvc5_delete(s2);
  }
  ASSERT_TRUE(cvc5_term_is_equal(value1, value2));
  {
    Cvc5* s3 = cvc5_new(d_tm);
    cvc5_set_logic(s3, "ALL");
    cvc5_set_option(s3, "produce-models", "true");
    Cvc5Term fun3 = cvc5_declare_fun(s3, "f3", 0, nullptr, d_int, true);
    std::vector<Cvc5Term> args = {deffun, zero};
    Cvc5Term apply =
        cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
    args = {fun3, apply};
    cvc5_assert_formula(
        s3, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
    cvc5_check_sat(s3);
    Cvc5Term value3 = cvc5_get_value(s3, fun3);
    ASSERT_TRUE(cvc5_term_is_equal(value1, value3));
    cvc5_delete(s3);
  }
}

#ifdef CVC5_USE_COCOA

TEST_F(TestCApiBlackSolver, basic_finite_field)
{
  cvc5_set_option(d_solver, "produce-models", "true");

  Cvc5Sort ff_sort = cvc5_mk_ff_sort(d_tm, "5", 10);
  Cvc5Term a = cvc5_mk_const(d_tm, ff_sort, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, ff_sort, "b");
  ASSERT_EQ(std::string("5"), cvc5_sort_ff_get_size(ff_sort));

  std::vector<Cvc5Term> args = {a, b};
  args = {
      cvc5_mk_term(d_tm, CVC5_KIND_FINITE_FIELD_MULT, args.size(), args.data()),
      cvc5_mk_ff_elem(d_tm, "1", ff_sort, 10)};
  Cvc5Term inv = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  args = {a, cvc5_mk_ff_elem(d_tm, "2", ff_sort, 10)};
  Cvc5Term a_is_two =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());

  cvc5_assert_formula(d_solver, inv);
  cvc5_assert_formula(d_solver, a_is_two);
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
  ASSERT_EQ(cvc5_term_get_ff_value(cvc5_get_value(d_solver, a)),
            std::string("2"));
  ASSERT_EQ(cvc5_term_get_ff_value(cvc5_get_value(d_solver, b)),
            std::string("-2"));

  args = {b, cvc5_mk_ff_elem(d_tm, "2", ff_sort, 10)};
  Cvc5Term b_is_two =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  cvc5_assert_formula(d_solver, b_is_two);
  ASSERT_FALSE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
}

TEST_F(TestCApiBlackSolver, basic_finite_field_base)
{
  cvc5_set_option(d_solver, "produce-models", "true");

  Cvc5Sort ff_sort = cvc5_mk_ff_sort(d_tm, "101", 2);
  Cvc5Term a = cvc5_mk_const(d_tm, ff_sort, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, ff_sort, "b");
  ASSERT_EQ(std::string("5"), cvc5_sort_ff_get_size(ff_sort));

  std::vector<Cvc5Term> args = {a, b};
  args = {
      cvc5_mk_term(d_tm, CVC5_KIND_FINITE_FIELD_MULT, args.size(), args.data()),
      cvc5_mk_ff_elem(d_tm, "1", ff_sort, 3)};
  Cvc5Term inv = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());

  args = {a, cvc5_mk_ff_elem(d_tm, "10", ff_sort, 2)};
  Cvc5Term a_is_two =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());

  cvc5_assert_formula(d_solver, inv);
  cvc5_assert_formula(d_solver, a_is_two);
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
  ASSERT_EQ(cvc5_term_get_ff_value(cvc5_get_value(d_solver, a)),
            std::string("2"));
  ASSERT_EQ(cvc5_term_get_ff_value(cvc5_get_value(d_solver, b)),
            std::string("-2"));

  args = {b, cvc5_mk_ff_elem(d_tm, "2", ff_sort, 10)};
  Cvc5Term b_is_two =
      cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  cvc5_assert_formula(d_solver, b_is_two);
  ASSERT_FALSE(cvc5_result_is_sat(cvc5_check_sat(d_solver)));
}
#endif  // CVC5_USE_COCOA

TEST_F(TestCApiBlackSolver, output1)
{
  ASSERT_DEATH(cvc5_is_output_on(nullptr, "inst"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_is_output_on(d_solver, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_is_output_on(d_solver, "foo-invalid"),
               "invalid output tag");

  ASSERT_DEATH(cvc5_get_output(nullptr, "inst", "<stdout>"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_output(d_solver, nullptr, "<stdout>"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_output(d_solver, "inst", nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_get_output(d_solver, "foo-invalid", "<stdout>"),
               "invalid output tag");

  ASSERT_DEATH(cvc5_close_output(nullptr, "<stdout>"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_close_output(d_solver, nullptr),
               "unexpected NULL argument");
  // should not fail
  cvc5_close_output(d_solver, "<stdout>");
}

TEST_F(TestCApiBlackSolver, output2)
{
  ASSERT_FALSE(cvc5_is_output_on(d_solver, "inst"));
  // noop if output tag is not enabled
  cvc5_get_output(d_solver, "inst", "<stdout>");
  cvc5_set_option(d_solver, "output", "inst");
  ASSERT_TRUE(cvc5_is_output_on(d_solver, "inst"));
  cvc5_get_output(d_solver, "inst", "<stdout>");
}

TEST_F(TestCApiBlackSolver, output3)
{
  cvc5_set_option(d_solver, "output", "post-asserts");
  cvc5_get_output(d_solver, "post-asserts", "<stdout>");

  testing::internal::CaptureStdout();

  std::vector<Cvc5Term> vars = {cvc5_mk_var(d_tm, d_bool, "b")};
  Cvc5Term g = cvc5_define_fun(
      d_solver, "g", vars.size(), vars.data(), d_bool, vars[0], true);
  std::vector<Cvc5Term> args = {g, cvc5_mk_true(d_tm)};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data())};
  Cvc5Term appnot = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  args = {cvc5_define_fun(
      d_solver, "f", 0, nullptr, d_bool, cvc5_mk_true(d_tm), true)};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()), appnot};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  cvc5_check_sat(d_solver);

  std::string out = testing::internal::GetCapturedStdout();
  std::stringstream expected;
  expected << ";; post-asserts start" << std::endl;
  expected << "(set-logic ALL)" << std::endl;
  expected << "(define-fun f () Bool true)" << std::endl;
  expected << "(define-fun g ((b Bool)) Bool b)" << std::endl;
  expected << "(assert false)" << std::endl;
  expected << "(check-sat)" << std::endl;
  expected << ";; post-asserts end" << std::endl;
  ASSERT_EQ(out, expected.str());
}

TEST_F(TestCApiBlackSolver, output4)
{
  const char* filename = "foo.out";
  cvc5_set_option(d_solver, "output", "post-asserts");
  cvc5_get_output(d_solver, "post-asserts", filename);

  std::vector<Cvc5Term> vars = {cvc5_mk_var(d_tm, d_bool, "b")};
  Cvc5Term g = cvc5_define_fun(
      d_solver, "g", vars.size(), vars.data(), d_bool, vars[0], true);
  std::vector<Cvc5Term> args = {g, cvc5_mk_true(d_tm)};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data())};
  Cvc5Term appnot = cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data());
  args = {cvc5_define_fun(
      d_solver, "f", 0, nullptr, d_bool, cvc5_mk_true(d_tm), true)};
  args = {cvc5_mk_term(d_tm, CVC5_KIND_NOT, args.size(), args.data()), appnot};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_OR, args.size(), args.data()));
  cvc5_check_sat(d_solver);

  cvc5_close_output(d_solver, filename);
  std::ifstream in(filename);
  std::stringstream out;
  out << in.rdbuf();
  std::stringstream expected;
  expected << ";; post-asserts start" << std::endl;
  expected << "(set-logic ALL)" << std::endl;
  expected << "(define-fun f () Bool true)" << std::endl;
  expected << "(define-fun g ((b Bool)) Bool b)" << std::endl;
  expected << "(assert false)" << std::endl;
  expected << "(check-sat)" << std::endl;
  expected << ";; post-asserts end" << std::endl;
  ASSERT_EQ(out.str(), expected.str());
  std::remove(filename);
}
}  // namespace cvc5::internal::test
