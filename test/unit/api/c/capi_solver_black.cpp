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
 * Black box testing of solver functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

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
    if (std::string(names[i]) == "verbose")
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

}  // namespace cvc5::internal::test
