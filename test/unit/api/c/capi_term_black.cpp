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
 * Black box testing of the guards of the C API functions.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackTerm : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_int = cvc5_get_integer_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
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
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackTerm, hash)
{
  ASSERT_DEATH(cvc5_term_hash(nullptr), "invalid term");
  (void)cvc5_term_hash(cvc5_mk_integer_int64(d_tm, 2));
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  Cvc5Term y = cvc5_mk_var(d_tm, d_int, "y");
  ASSERT_EQ(cvc5_term_hash(x), cvc5_term_hash(x));
  ASSERT_NE(cvc5_term_hash(x), cvc5_term_hash(y));
}

TEST_F(TestCApiBlackTerm, copy_release)
{
  ASSERT_DEATH(cvc5_term_copy(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_release(nullptr), "invalid term");
  Cvc5Term tint = cvc5_mk_integer_int64(d_tm, 2);
  size_t hash1 = cvc5_term_hash(tint);
  Cvc5Term tint_copy = cvc5_term_copy(tint);
  size_t hash2 = cvc5_term_hash(tint_copy);
  ASSERT_EQ(hash1, hash2);
  cvc5_term_release(tint);
  ASSERT_EQ(cvc5_term_hash(tint), cvc5_term_hash(tint_copy));
  cvc5_term_release(tint);
  // we cannot reliably check that querying on the (now freed) term fails
  // unless ASAN is enabled
}

TEST_F(TestCApiBlackTerm, compare)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_var(d_tm, d_uninterpreted, "y");
  ASSERT_DEATH(cvc5_term_compare(x, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_compare(nullptr, y), "invalid term");
  ASSERT_FALSE(cvc5_term_is_equal(x, nullptr));
  ASSERT_TRUE(cvc5_term_is_disequal(x, nullptr));
  ASSERT_EQ(cvc5_term_compare(x, x), 0);
  ASSERT_NE(cvc5_term_compare(x, y), 0);
}

TEST_F(TestCApiBlackTerm, get_id)
{
  ASSERT_DEATH(cvc5_term_get_id(nullptr), "invalid term");
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  Cvc5Term y = cvc5_term_copy(x);
  Cvc5Term z = cvc5_mk_var(d_tm, d_int, "z");
  (void)cvc5_term_get_id(x);
  ASSERT_EQ(cvc5_term_get_id(x), cvc5_term_get_id(y));
  ASSERT_NE(cvc5_term_get_id(x), cvc5_term_get_id(z));
  cvc5_term_release(y);
}

TEST_F(TestCApiBlackTerm, get_kind)
{
  std::vector<Cvc5Sort> domain = {d_uninterpreted};
  Cvc5Sort fun_sort1 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort fun_sort2 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);

  ASSERT_DEATH(cvc5_term_get_kind(nullptr), "invalid term");

  Cvc5Term x = cvc5_mk_var(d_tm, d_uninterpreted, "x");
  ASSERT_EQ(cvc5_term_get_kind(x), CVC5_KIND_VARIABLE);
  Cvc5Term y = cvc5_mk_var(d_tm, d_uninterpreted, "y");
  ASSERT_EQ(cvc5_term_get_kind(y), CVC5_KIND_VARIABLE);

  Cvc5Term f = cvc5_mk_var(d_tm, fun_sort1, "f");
  ASSERT_EQ(cvc5_term_get_kind(f), CVC5_KIND_VARIABLE);
  Cvc5Term p = cvc5_mk_var(d_tm, fun_sort2, "p");
  ASSERT_EQ(cvc5_term_get_kind(p), CVC5_KIND_VARIABLE);

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  ASSERT_EQ(cvc5_term_get_kind(zero), CVC5_KIND_CONST_INTEGER);

  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(f_x), CVC5_KIND_APPLY_UF);
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(f_y), CVC5_KIND_APPLY_UF);
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(sum), CVC5_KIND_ADD);
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(p_0), CVC5_KIND_APPLY_UF);
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(p_f_y), CVC5_KIND_APPLY_UF);

  // Sequence kinds do not exist internally, test that the API properly
  // converts them back.
  Cvc5Sort seq_sort = cvc5_mk_sequence_sort(d_tm, d_int);
  Cvc5Term s = cvc5_mk_const(d_tm, seq_sort, "s");
  args = {s, s};
  Cvc5Term ss =
      cvc5_mk_term(d_tm, CVC5_KIND_SEQ_CONCAT, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(ss), CVC5_KIND_SEQ_CONCAT);
}

TEST_F(TestCApiBlackTerm, get_sort)
{
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 8);
  std::vector<Cvc5Sort> domain = {bv_sort};
  Cvc5Sort fun_sort1 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  domain = {d_int};
  Cvc5Sort fun_sort2 =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool);

  ASSERT_DEATH(cvc5_term_get_sort(nullptr), "invalid term");

  Cvc5Term x = cvc5_mk_var(d_tm, bv_sort, "x");
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(x), bv_sort));
  Cvc5Term y = cvc5_mk_var(d_tm, bv_sort, "y");
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(x), cvc5_term_get_sort(y)));

  Cvc5Term f = cvc5_mk_var(d_tm, fun_sort1, "f");
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(f), fun_sort1));
  Cvc5Term p = cvc5_mk_var(d_tm, fun_sort2, "p");
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(p), fun_sort2));

  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(zero), d_int));

  std::vector<Cvc5Term> args = {f, x};
  Cvc5Term f_x =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(f_x), d_int));
  args = {f, y};
  Cvc5Term f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(f_y), d_int));
  args = {f_x, f_y};
  Cvc5Term sum = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(sum), d_int));
  args = {p, zero};
  Cvc5Term p_0 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(p_0), d_bool));
  args = {p, f_y};
  Cvc5Term p_f_y =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(p_f_y), d_bool));
  ASSERT_EQ(cvc5_term_get_kind(p_f_y), CVC5_KIND_APPLY_UF);
}

TEST_F(TestCApiBlackTerm, get_op)
{
  ASSERT_DEATH(cvc5_term_has_op(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_op(nullptr), "invalid term");

  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 8);
  Cvc5Sort arr_sort = cvc5_mk_array_sort(d_tm, bv_sort, d_int);
  std::vector<Cvc5Sort> domain = {d_int};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), bv_sort);

  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term a = cvc5_mk_const(d_tm, arr_sort, "a");
  Cvc5Term b = cvc5_mk_const(d_tm, bv_sort, "b");

  ASSERT_FALSE(cvc5_term_has_op(x));
  ASSERT_DEATH(cvc5_term_get_op(x), "expected Term to have an Op");

  std::vector<Cvc5Term> args = {a, b};
  Cvc5Term ab = cvc5_mk_term(d_tm, CVC5_KIND_SELECT, args.size(), args.data());
  ASSERT_TRUE(cvc5_term_has_op(ab));
  ASSERT_FALSE(cvc5_op_is_indexed(cvc5_term_get_op(ab)));

  std::vector<uint32_t> idxs = {4, 0};
  Cvc5Op ext =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  args = {b};
  Cvc5Term extb = cvc5_mk_term_from_op(d_tm, ext, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(extb), CVC5_KIND_BITVECTOR_EXTRACT);
  // can compare directly to a Kind (will invoke Op constructor)
  ASSERT_TRUE(cvc5_term_has_op(extb));
  ASSERT_TRUE(cvc5_op_is_indexed(cvc5_term_get_op(extb)));
  ASSERT_TRUE(cvc5_op_is_equal(cvc5_term_get_op(extb), ext));

  idxs = {4};
  Cvc5Op bit =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_BIT, idxs.size(), idxs.data());
  Cvc5Term bitb = cvc5_mk_term_from_op(d_tm, bit, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_kind(bitb), CVC5_KIND_BITVECTOR_BIT);
  ASSERT_TRUE(cvc5_term_has_op(bitb));
  ASSERT_TRUE(cvc5_op_is_equal(cvc5_term_get_op(bitb), bit));
  ASSERT_TRUE(cvc5_op_is_indexed(cvc5_term_get_op(bitb)));
  ASSERT_EQ(cvc5_op_get_num_indices(bit), 1);
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_op_get_index(bit, 0),
                                 cvc5_mk_integer_int64(d_tm, 4)));

  Cvc5Term f = cvc5_mk_const(d_tm, fun_sort, "f");
  args = {f, x};
  Cvc5Term fx =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  ASSERT_FALSE(cvc5_term_has_op(f));
  ASSERT_DEATH(cvc5_term_get_op(f), "expected Term to have an Op");
  ASSERT_TRUE(cvc5_term_has_op(fx));

  // testing rebuild from op and children
  ASSERT_TRUE(cvc5_term_is_equal(
      fx,
      cvc5_mk_term_from_op(
          d_tm, cvc5_term_get_op(fx), args.size(), args.data())));

  // Test Datatypes Ops
  Cvc5Sort sort = cvc5_mk_param_sort(d_tm, "T");
  std::vector<Cvc5Sort> sorts = {sort};
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl_with_params(
      d_tm, "paramlist", sorts.size(), sorts.data(), false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", sort);
  cvc5_dt_cons_decl_add_selector_self(cons, "tail");
  cvc5_dt_decl_add_constructor(decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);
  Cvc5Sort list_sort = cvc5_mk_dt_sort(d_tm, decl);
  sorts = {d_int};
  Cvc5Sort int_list_sort =
      cvc5_sort_instantiate(list_sort, sorts.size(), sorts.data());

  Cvc5Term c = cvc5_mk_const(d_tm, int_list_sort, "c");
  Cvc5Datatype list = cvc5_sort_get_datatype(list_sort);
  // list datatype constructor and selector operator terms
  Cvc5Term cons_term =
      cvc5_dt_cons_get_term(cvc5_dt_get_constructor_by_name(list, "cons"));
  Cvc5Term nil_term =
      cvc5_dt_cons_get_term(cvc5_dt_get_constructor_by_name(list, "nil"));
  Cvc5Term head_term = cvc5_dt_sel_get_term(cvc5_dt_get_selector(list, "head"));
  Cvc5Term tail_term = cvc5_dt_sel_get_term(cvc5_dt_get_selector(list, "tail"));

  args = {nil_term};
  Cvc5Term apply_nil_term =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, args.size(), args.data());
  args = {cons_term, cvc5_mk_integer_int64(d_tm, 0), apply_nil_term};
  Cvc5Term apply_cons_term =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_CONSTRUCTOR, args.size(), args.data());
  args = {head_term, apply_cons_term};
  Cvc5Term apply_head_term =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, args.size(), args.data());
  args = {tail_term, apply_cons_term};
  Cvc5Term apply_tail_term =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_SELECTOR, args.size(), args.data());

  ASSERT_FALSE(cvc5_term_has_op(c));
  ASSERT_TRUE(cvc5_term_has_op(apply_nil_term));
  ASSERT_TRUE(cvc5_term_has_op(apply_cons_term));
  ASSERT_TRUE(cvc5_term_has_op(apply_head_term));
  ASSERT_TRUE(cvc5_term_has_op(apply_tail_term));

  // Test rebuilding
  args.clear();
  for (size_t i = 0, n = cvc5_term_get_num_children(apply_head_term); i < n;
       ++i)
  {
    args.push_back(cvc5_term_get_child(apply_head_term, i));
  }
  ASSERT_TRUE(cvc5_term_is_equal(
      apply_head_term,
      cvc5_mk_term_from_op(
          d_tm, cvc5_term_get_op(apply_head_term), args.size(), args.data())));
}

TEST_F(TestCApiBlackTerm, has_get_symbol)
{
  ASSERT_DEATH(cvc5_term_has_symbol(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_symbol(nullptr), "invalid term");

  Cvc5Term t = cvc5_mk_true(d_tm);
  Cvc5Term c = cvc5_mk_const(d_tm, d_bool, "|\\|");

  ASSERT_FALSE(cvc5_term_has_symbol(t));
  ASSERT_TRUE(cvc5_term_has_symbol(c));

  ASSERT_DEATH(cvc5_term_get_symbol(t), "cannot get symbol");
  ASSERT_EQ(cvc5_term_get_symbol(c), std::string("|\\|"));
}

TEST_F(TestCApiBlackTerm, assignment)
{
  Cvc5Term t1 = cvc5_mk_integer_int64(d_tm, 1);
  Cvc5Term t2 = cvc5_term_copy(t1);
  t2 = cvc5_mk_integer_int64(d_tm, 2);
  ASSERT_TRUE(cvc5_term_is_equal(t1, cvc5_mk_integer_int64(d_tm, 1)));
  ASSERT_TRUE(cvc5_term_is_equal(t2, cvc5_mk_integer_int64(d_tm, 2)));
  ASSERT_FALSE(cvc5_term_is_equal(t1, t2));
  cvc5_term_release(t1);
  ASSERT_TRUE(cvc5_term_is_equal(t1, cvc5_mk_integer_int64(d_tm, 1)));
  ASSERT_TRUE(cvc5_term_is_equal(t2, cvc5_mk_integer_int64(d_tm, 2)));
  ASSERT_FALSE(cvc5_term_is_equal(t1, t2));
}

TEST_F(TestCApiBlackTerm, children)
{
  ASSERT_DEATH(cvc5_term_get_num_children(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_child(nullptr, 0), "invalid term");
  // simple term 2+3
  Cvc5Term two = cvc5_mk_integer_int64(d_tm, 2);
  std::vector<Cvc5Term> args = {two, cvc5_mk_integer_int64(d_tm, 3)};
  Cvc5Term t1 = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  ASSERT_EQ(cvc5_term_get_num_children(t1), 2);
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_term_get_child(t1, 0), two));

  for (size_t i = 0, n = cvc5_term_get_num_children(t1); i < n; ++i)
  {
    (void)cvc5_term_get_child(t1, i);
  }

  // apply term f(2)
  std::vector<Cvc5Sort> domain = {d_int};
  Cvc5Sort fun_sort =
      cvc5_mk_fun_sort(d_tm, domain.size(), domain.data(), d_int);
  Cvc5Term f = cvc5_mk_const(d_tm, fun_sort, "f");
  args = {f, two};
  Cvc5Term t2 =
      cvc5_mk_term(d_tm, CVC5_KIND_APPLY_UF, args.size(), args.data());
  // due to our higher-order view of terms, we treat f as a child of APPLY_UF
  ASSERT_EQ(cvc5_term_get_num_children(t2), 2);
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_term_get_child(t2, 0), f));
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_term_get_child(t2, 1), two));
}

TEST_F(TestCApiBlackTerm, get_integer)
{
  ASSERT_DEATH(cvc5_mk_integer(nullptr, "2"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, nullptr), "unexpected NULL argument");

  Cvc5Term int1 = cvc5_mk_integer(d_tm, "-18446744073709551616");
  Cvc5Term int2 = cvc5_mk_integer(d_tm, "-18446744073709551615");
  Cvc5Term int3 = cvc5_mk_integer(d_tm, "-4294967296");
  Cvc5Term int4 = cvc5_mk_integer(d_tm, "-4294967295");
  Cvc5Term int5 = cvc5_mk_integer(d_tm, "-10");
  Cvc5Term int6 = cvc5_mk_integer(d_tm, "0");
  Cvc5Term int7 = cvc5_mk_integer(d_tm, "10");
  Cvc5Term int8 = cvc5_mk_integer(d_tm, "4294967295");
  Cvc5Term int9 = cvc5_mk_integer(d_tm, "4294967296");
  Cvc5Term int10 = cvc5_mk_integer(d_tm, "18446744073709551615");
  Cvc5Term int11 = cvc5_mk_integer(d_tm, "18446744073709551616");
  Cvc5Term int12 = cvc5_mk_integer(d_tm, "-0");

  ASSERT_DEATH(cvc5_mk_integer(d_tm, ""), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "-"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "-1-"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "0.0"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "-0.1"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "012"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "0000"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "-01"), "invalid argument");
  ASSERT_DEATH(cvc5_mk_integer(d_tm, "-00"), "invalid argument");

  ASSERT_DEATH(cvc5_term_is_int32_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_uint32_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_int64_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_uint64_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_integer_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_integer_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_int32_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_int64_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_uint32_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_uint64_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_real_or_integer_value_sign(nullptr),
               "invalid term");

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int1) && !cvc5_term_is_uint32_value(int1)
      && !cvc5_term_is_int64_value(int1) && !cvc5_term_is_uint64_value(int1)
      && cvc5_term_is_integer_value(int1));
  ASSERT_EQ(cvc5_term_get_integer_value(int1),
            std::string("-18446744073709551616"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int1), -1);

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int2) && !cvc5_term_is_uint32_value(int2)
      && !cvc5_term_is_int64_value(int2) && !cvc5_term_is_uint64_value(int2)
      && cvc5_term_is_integer_value(int2));
  ASSERT_EQ(cvc5_term_get_integer_value(int2),
            std::string("-18446744073709551615"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int2), -1);

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int3) && !cvc5_term_is_uint32_value(int3)
      && cvc5_term_is_int64_value(int3) && !cvc5_term_is_uint64_value(int3)
      && cvc5_term_is_integer_value(int3));
  ASSERT_EQ(cvc5_term_get_integer_value(int3), std::string("-4294967296"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int3), -1);
  ASSERT_EQ(cvc5_term_get_int64_value(int3), -4294967296);

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int4) && !cvc5_term_is_uint32_value(int4)
      && cvc5_term_is_int64_value(int4) && !cvc5_term_is_uint64_value(int4)
      && cvc5_term_is_integer_value(int4));
  ASSERT_EQ(cvc5_term_get_integer_value(int4), std::string("-4294967295"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int4), -1);
  ASSERT_EQ(cvc5_term_get_int64_value(int4), -4294967295);

  ASSERT_TRUE(cvc5_term_is_int32_value(int5) && !cvc5_term_is_uint32_value(int5)
              && cvc5_term_is_int64_value(int5)
              && !cvc5_term_is_uint64_value(int5)
              && cvc5_term_is_integer_value(int5));
  ASSERT_EQ(cvc5_term_get_integer_value(int5), std::string("-10"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int5), -1);
  ASSERT_EQ(cvc5_term_get_int32_value(int5), -10);
  ASSERT_EQ(cvc5_term_get_int64_value(int5), -10);

  ASSERT_TRUE(cvc5_term_is_int32_value(int6) && cvc5_term_is_uint32_value(int6)
              && cvc5_term_is_int64_value(int6)
              && cvc5_term_is_uint64_value(int6)
              && cvc5_term_is_integer_value(int6));
  ASSERT_EQ(cvc5_term_get_integer_value(int6), std::string("0"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int6), 0);
  ASSERT_EQ(cvc5_term_get_int32_value(int6), 0);
  ASSERT_EQ(cvc5_term_get_int64_value(int6), 0);
  ASSERT_EQ(cvc5_term_get_uint32_value(int6), 0);
  ASSERT_EQ(cvc5_term_get_uint64_value(int6), 0);

  ASSERT_TRUE(cvc5_term_is_int32_value(int7) && cvc5_term_is_uint32_value(int7)
              && cvc5_term_is_int64_value(int7)
              && cvc5_term_is_uint64_value(int7)
              && cvc5_term_is_integer_value(int7));
  ASSERT_EQ(cvc5_term_get_integer_value(int7), std::string("10"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int7), 1);
  ASSERT_EQ(cvc5_term_get_int32_value(int7), 10);
  ASSERT_EQ(cvc5_term_get_int64_value(int7), 10);
  ASSERT_EQ(cvc5_term_get_uint32_value(int7), 10);
  ASSERT_EQ(cvc5_term_get_uint64_value(int7), 10);

  ASSERT_TRUE(!cvc5_term_is_int32_value(int8) && cvc5_term_is_uint32_value(int8)
              && cvc5_term_is_int64_value(int8)
              && cvc5_term_is_uint64_value(int8)
              && cvc5_term_is_integer_value(int8));
  ASSERT_EQ(cvc5_term_get_integer_value(int8), std::string("4294967295"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int8), 1);
  ASSERT_EQ(cvc5_term_get_int64_value(int8), 4294967295);
  ASSERT_EQ(cvc5_term_get_uint32_value(int8), 4294967295);
  ASSERT_EQ(cvc5_term_get_uint64_value(int8), 4294967295);

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int9) && !cvc5_term_is_uint32_value(int9)
      && cvc5_term_is_int64_value(int9) && cvc5_term_is_uint64_value(int9)
      && cvc5_term_is_integer_value(int9));
  ASSERT_EQ(cvc5_term_get_integer_value(int9), std::string("4294967296"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int9), 1);
  ASSERT_EQ(cvc5_term_get_int64_value(int9), 4294967296);
  ASSERT_EQ(cvc5_term_get_uint64_value(int9), 4294967296);

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int10) && !cvc5_term_is_uint32_value(int10)
      && !cvc5_term_is_int64_value(int10) && cvc5_term_is_uint64_value(int10)
      && cvc5_term_is_integer_value(int10));
  ASSERT_EQ(cvc5_term_get_integer_value(int10),
            std::string("18446744073709551615"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int10), 1);
  ASSERT_EQ(cvc5_term_get_uint64_value(int10), 18446744073709551615ull);

  ASSERT_TRUE(
      !cvc5_term_is_int32_value(int11) && !cvc5_term_is_uint32_value(int11)
      && !cvc5_term_is_int64_value(int11) && !cvc5_term_is_uint64_value(int11)
      && cvc5_term_is_integer_value(int11));
  ASSERT_EQ(cvc5_term_get_integer_value(int11),
            std::string("18446744073709551616"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int11), 1);

  ASSERT_TRUE(
      cvc5_term_is_int32_value(int12) && cvc5_term_is_uint32_value(int12)
      && cvc5_term_is_int64_value(int12) && cvc5_term_is_uint64_value(int12)
      && cvc5_term_is_integer_value(int12));
  ASSERT_EQ(cvc5_term_get_integer_value(int12), std::string("0"));
  ASSERT_EQ(cvc5_term_get_real_or_integer_value_sign(int12), 0);
  ASSERT_EQ(cvc5_term_get_int32_value(int12), 0);
  ASSERT_EQ(cvc5_term_get_int64_value(int12), 0);
  ASSERT_EQ(cvc5_term_get_uint32_value(int12), 0);
  ASSERT_EQ(cvc5_term_get_uint64_value(int12), 0);
}

TEST_F(TestCApiBlackTerm, get_string)
{
  ASSERT_DEATH(cvc5_mk_string(nullptr, "abcde", false),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_is_string_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_string_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_mk_string(d_tm, nullptr, false),
               "unexpected NULL argument");
  Cvc5Term s1 = cvc5_mk_string(d_tm, "abcde", false);
  ASSERT_TRUE(cvc5_term_is_string_value(s1));
  ASSERT_EQ(cvc5_term_get_string_value(s1), std::wstring(L"abcde"));
}

TEST_F(TestCApiBlackTerm, get_real)
{
  int32_t num32;
  uint32_t den32;
  int64_t num64;
  uint64_t den64;

  ASSERT_DEATH(cvc5_mk_real(nullptr, "2"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_real(d_tm, nullptr), "unexpected NULL argument");

  Cvc5Term real1 = cvc5_mk_real(d_tm, "0");
  Cvc5Term real2 = cvc5_mk_real(d_tm, ".0");
  Cvc5Term real3 = cvc5_mk_real(d_tm, "-17");
  Cvc5Term real4 = cvc5_mk_real(d_tm, "-3/5");
  Cvc5Term real5 = cvc5_mk_real(d_tm, "12.7");
  Cvc5Term real6 = cvc5_mk_real(d_tm, "1/4294967297");
  Cvc5Term real7 = cvc5_mk_real(d_tm, "4294967297");
  Cvc5Term real8 = cvc5_mk_real(d_tm, "1/18446744073709551617");
  Cvc5Term real9 = cvc5_mk_real(d_tm, "18446744073709551617");
  Cvc5Term real10 = cvc5_mk_real(d_tm, "2343.2343");

  ASSERT_DEATH(cvc5_term_is_real32_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_real64_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_real_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_real_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_real32_value(nullptr, &num32, &den32),
               "invalid term");
  ASSERT_DEATH(cvc5_term_get_real32_value(real1, nullptr, &den32),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_real32_value(real1, &num32, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_real64_value(real1, nullptr, &den64),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_real64_value(real1, &num64, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_real64_value(nullptr, &num64, &den64),
               "invalid term");
  ASSERT_DEATH(cvc5_term_get_real_or_integer_value_sign(nullptr),
               "invalid term");

  ASSERT_TRUE(cvc5_term_is_real_value(real1) && cvc5_term_is_real64_value(real1)
              && cvc5_term_is_real32_value(real1));
  ASSERT_TRUE(cvc5_term_is_real_value(real2) && cvc5_term_is_real64_value(real2)
              && cvc5_term_is_real32_value(real2));
  ASSERT_TRUE(cvc5_term_is_real_value(real3) && cvc5_term_is_real64_value(real3)
              && cvc5_term_is_real32_value(real3));
  ASSERT_TRUE(cvc5_term_is_real_value(real4) && cvc5_term_is_real64_value(real4)
              && cvc5_term_is_real32_value(real4));
  ASSERT_TRUE(cvc5_term_is_real_value(real5) && cvc5_term_is_real64_value(real5)
              && cvc5_term_is_real32_value(real5));
  ASSERT_TRUE(cvc5_term_is_real_value(real6)
              && cvc5_term_is_real64_value(real6));
  ASSERT_TRUE(cvc5_term_is_real_value(real7)
              && cvc5_term_is_real64_value(real7));
  ASSERT_TRUE(cvc5_term_is_real_value(real8));
  ASSERT_TRUE(cvc5_term_is_real_value(real9));
  ASSERT_TRUE(cvc5_term_is_real_value(real10));

  cvc5_term_get_real32_value(real1, &num32, &den32);
  ASSERT_EQ(num32, 0);
  ASSERT_EQ(den32, 1);
  cvc5_term_get_real64_value(real1, &num64, &den64);
  ASSERT_EQ(num64, 0);
  ASSERT_EQ(den64, 1);
  ASSERT_EQ(cvc5_term_get_real_value(real1), std::string("0/1"));

  cvc5_term_get_real32_value(real2, &num32, &den32);
  ASSERT_EQ(num32, 0);
  ASSERT_EQ(den32, 1);
  cvc5_term_get_real64_value(real2, &num64, &den64);
  ASSERT_EQ(num64, 0);
  ASSERT_EQ(den64, 1);
  ASSERT_EQ(cvc5_term_get_real_value(real2), std::string("0/1"));

  cvc5_term_get_real32_value(real3, &num32, &den32);
  ASSERT_EQ(num32, -17);
  ASSERT_EQ(den32, 1);
  cvc5_term_get_real64_value(real3, &num64, &den64);
  ASSERT_EQ(num64, -17);
  ASSERT_EQ(den64, 1);
  ASSERT_EQ(cvc5_term_get_real_value(real3), std::string("-17/1"));

  cvc5_term_get_real32_value(real4, &num32, &den32);
  ASSERT_EQ(num32, -3);
  ASSERT_EQ(den32, 5);
  cvc5_term_get_real64_value(real4, &num64, &den64);
  ASSERT_EQ(num64, -3);
  ASSERT_EQ(den64, 5);
  ASSERT_EQ(cvc5_term_get_real_value(real4), std::string("-3/5"));

  cvc5_term_get_real32_value(real5, &num32, &den32);
  ASSERT_EQ(num32, 127);
  ASSERT_EQ(den32, 10);
  cvc5_term_get_real64_value(real5, &num64, &den64);
  ASSERT_EQ(num64, 127);
  ASSERT_EQ(den64, 10);
  ASSERT_EQ(cvc5_term_get_real_value(real5), std::string("127/10"));

  cvc5_term_get_real64_value(real6, &num64, &den64);
  ASSERT_EQ(num64, 1);
  ASSERT_EQ(den64, 4294967297);
  ASSERT_EQ(cvc5_term_get_real_value(real6), std::string("1/4294967297"));

  cvc5_term_get_real64_value(real7, &num64, &den64);
  ASSERT_EQ(num64, 4294967297);
  ASSERT_EQ(den64, 1);
  ASSERT_EQ(cvc5_term_get_real_value(real7), std::string("4294967297/1"));

  ASSERT_EQ(cvc5_term_get_real_value(real8),
            std::string("1/18446744073709551617"));

  ASSERT_EQ(cvc5_term_get_real_value(real9),
            std::string("18446744073709551617/1"));

  ASSERT_EQ(cvc5_term_get_real_value(real10), std::string("23432343/10000"));
}

TEST_F(TestCApiBlackTerm, get_const_array_base)
{
  Cvc5Sort arr_sort = cvc5_mk_array_sort(d_tm, d_int, d_int);
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  Cvc5Term const_arr = cvc5_mk_const_array(d_tm, arr_sort, one);

  ASSERT_DEATH(cvc5_term_is_const_array(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_const_array_base(nullptr), "invalid term");

  ASSERT_TRUE(cvc5_term_is_const_array(const_arr));
  ASSERT_TRUE(
      cvc5_term_is_equal(cvc5_term_get_const_array_base(const_arr), one));

  Cvc5Term a = cvc5_mk_const(d_tm, arr_sort, "a");
  ASSERT_DEATH(cvc5_term_get_const_array_base(a), "invalid argument");
  ASSERT_DEATH(cvc5_term_get_const_array_base(one), "invalid argument");
}

TEST_F(TestCApiBlackTerm, get_boolean_value)
{
  Cvc5Term b1 = cvc5_mk_true(d_tm);
  Cvc5Term b2 = cvc5_mk_false(d_tm);

  ASSERT_DEATH(cvc5_term_is_boolean_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_boolean_value(nullptr), "invalid term");
  ASSERT_TRUE(cvc5_term_is_boolean_value(b1));
  ASSERT_TRUE(cvc5_term_is_boolean_value(b2));
  ASSERT_TRUE(cvc5_term_get_boolean_value(b1));
  ASSERT_FALSE(cvc5_term_get_boolean_value(b2));
}

TEST_F(TestCApiBlackTerm, get_bv_value)
{
  ASSERT_DEATH(cvc5_mk_bv_uint64(nullptr, 8, 15), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_is_bv_value(nullptr), "invalid term");

  Cvc5Term b1 = cvc5_mk_bv_uint64(d_tm, 8, 15);
  Cvc5Term b2 = cvc5_mk_bv(d_tm, 8, "00001111", 2);
  Cvc5Term b3 = cvc5_mk_bv(d_tm, 8, "15", 10);
  Cvc5Term b4 = cvc5_mk_bv(d_tm, 8, "0f", 16);
  Cvc5Term b5 = cvc5_mk_bv(d_tm, 9, "00001111", 2);
  Cvc5Term b6 = cvc5_mk_bv(d_tm, 9, "15", 10);
  Cvc5Term b7 = cvc5_mk_bv(d_tm, 9, "0f", 16);

  ASSERT_TRUE(cvc5_term_is_bv_value(b1));
  ASSERT_TRUE(cvc5_term_is_bv_value(b2));
  ASSERT_TRUE(cvc5_term_is_bv_value(b3));
  ASSERT_TRUE(cvc5_term_is_bv_value(b4));
  ASSERT_TRUE(cvc5_term_is_bv_value(b5));
  ASSERT_TRUE(cvc5_term_is_bv_value(b6));
  ASSERT_TRUE(cvc5_term_is_bv_value(b7));

  ASSERT_EQ(std::string("00001111"), cvc5_term_get_bv_value(b1, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b1, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b1, 16));
  ASSERT_EQ(std::string("00001111"), cvc5_term_get_bv_value(b2, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b2, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b2, 16));
  ASSERT_EQ(std::string("00001111"), cvc5_term_get_bv_value(b3, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b3, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b3, 16));
  ASSERT_EQ(std::string("00001111"), cvc5_term_get_bv_value(b4, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b4, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b4, 16));
  ASSERT_EQ(std::string("000001111"), cvc5_term_get_bv_value(b5, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b5, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b5, 16));
  ASSERT_EQ(std::string("000001111"), cvc5_term_get_bv_value(b6, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b6, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b6, 16));
  ASSERT_EQ(std::string("000001111"), cvc5_term_get_bv_value(b7, 2));
  ASSERT_EQ(std::string("15"), cvc5_term_get_bv_value(b7, 10));
  ASSERT_EQ(std::string("f"), cvc5_term_get_bv_value(b7, 16));
}

TEST_F(TestCApiBlackTerm, is_ff_value)
{
  ASSERT_DEATH(cvc5_term_is_ff_value(nullptr), "invalid term");
  Cvc5Sort fs = cvc5_mk_ff_sort(d_tm, "7", 10);
  Cvc5Term fv = cvc5_mk_ff_elem(d_tm, "1", fs, 10);
  ASSERT_TRUE(cvc5_term_is_ff_value(fv));
  Cvc5Term b1 = cvc5_mk_bv_uint64(d_tm, 8, 15);
  ASSERT_FALSE(cvc5_term_is_ff_value(b1));
}

TEST_F(TestCApiBlackTerm, get_ff_value)
{
  ASSERT_DEATH(cvc5_term_get_ff_value(nullptr), "invalid term");
  Cvc5Sort fs = cvc5_mk_ff_sort(d_tm, "7", 10);
  Cvc5Term fv = cvc5_mk_ff_elem(d_tm, "1", fs, 10);
  ASSERT_EQ(std::string("1"), cvc5_term_get_ff_value(fv));
  Cvc5Term b1 = cvc5_mk_bv_uint64(d_tm, 8, 15);
  ASSERT_DEATH(cvc5_term_get_ff_value(b1),
               "expected Term to be a finite field value");
}

TEST_F(TestCApiBlackTerm, get_uninterpreted_sort_value)
{
  ASSERT_DEATH(cvc5_term_get_uninterpreted_sort_value(nullptr), "invalid term");
  cvc5_set_option(d_solver, "produce-models", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  Cvc5Term y = cvc5_mk_const(d_tm, d_uninterpreted, "y");
  std::vector<Cvc5Term> args = {x, y};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_sat(res));
  Cvc5Term vx = cvc5_get_value(d_solver, x);
  Cvc5Term vy = cvc5_get_value(d_solver, y);
  ASSERT_TRUE(cvc5_term_is_uninterpreted_sort_value(vx));
  ASSERT_TRUE(cvc5_term_is_uninterpreted_sort_value(vy));
  ASSERT_EQ(std::string(cvc5_term_get_uninterpreted_sort_value(vx)),
            cvc5_term_get_uninterpreted_sort_value(vy));
}

TEST_F(TestCApiBlackTerm, is_rm_value)
{
  ASSERT_DEATH(cvc5_term_is_rm_value(nullptr), "invalid term");
  ASSERT_FALSE(cvc5_term_is_rm_value(cvc5_mk_integer_int64(d_tm, 15)));
  ASSERT_TRUE(cvc5_term_is_rm_value(
      cvc5_mk_rm(d_tm, CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN)));
  ASSERT_FALSE(
      cvc5_term_is_rm_value(cvc5_mk_const(d_tm, cvc5_get_rm_sort(d_tm), "")));
}

TEST_F(TestCApiBlackTerm, get_rm_value)
{
  ASSERT_DEATH(cvc5_term_get_rm_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_rm_value(cvc5_mk_integer_int64(d_tm, 15)),
               "invalid argument");

  ASSERT_EQ(cvc5_term_get_rm_value(
                cvc5_mk_rm(d_tm, CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN)),
            CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN);
  ASSERT_EQ(cvc5_term_get_rm_value(
                cvc5_mk_rm(d_tm, CVC5_RM_ROUND_NEAREST_TIES_TO_AWAY)),
            CVC5_RM_ROUND_NEAREST_TIES_TO_AWAY);
  ASSERT_EQ(
      cvc5_term_get_rm_value(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_TOWARD_POSITIVE)),
      CVC5_RM_ROUND_TOWARD_POSITIVE);
  ASSERT_EQ(
      cvc5_term_get_rm_value(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_TOWARD_NEGATIVE)),
      CVC5_RM_ROUND_TOWARD_NEGATIVE);
  ASSERT_EQ(cvc5_term_get_rm_value(cvc5_mk_rm(d_tm, CVC5_RM_ROUND_TOWARD_ZERO)),
            CVC5_RM_ROUND_TOWARD_ZERO);
}

TEST_F(TestCApiBlackTerm, get_tuple)
{
  Cvc5Term t1 = cvc5_mk_integer_int64(d_tm, 15);
  Cvc5Term t2 = cvc5_mk_real_num_den(d_tm, 17, 25);
  Cvc5Term t3 = cvc5_mk_string(d_tm, "abc", false);
  std::vector<Cvc5Term> args = {t1, t2, t3};
  Cvc5Term tup = cvc5_mk_tuple(d_tm, args.size(), args.data());

  size_t size;
  ASSERT_DEATH(cvc5_term_get_tuple_value(nullptr, &size), "invalid term");
  ASSERT_DEATH(cvc5_term_get_tuple_value(tup, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_is_tuple_value(nullptr), "invalid term");

  ASSERT_TRUE(cvc5_term_is_tuple_value(tup));
  const Cvc5Term* val = cvc5_term_get_tuple_value(tup, &size);
  ASSERT_EQ(size, 3);
  ASSERT_TRUE(cvc5_term_is_equal(val[0], t1));
  ASSERT_TRUE(cvc5_term_is_equal(val[1], t2));
  ASSERT_TRUE(cvc5_term_is_equal(val[2], t3));
}

TEST_F(TestCApiBlackTerm, get_fp_value)
{
  uint32_t ew, sw;
  Cvc5Term res;
  Cvc5Term bv_val = cvc5_mk_bv(d_tm, 16, "0000110000000011", 2);
  Cvc5Term fp_val = cvc5_mk_fp(d_tm, 5, 11, bv_val);

  ASSERT_DEATH(cvc5_term_is_fp_value(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_fp_pos_zero(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_fp_neg_zero(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_fp_pos_inf(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_fp_neg_inf(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_is_fp_nan(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_fp_value(nullptr, &ew, &sw, &res), "invalid term");
  ASSERT_DEATH(cvc5_term_get_fp_value(fp_val, nullptr, &sw, &res),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_fp_value(fp_val, &ew, nullptr, &res),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_fp_value(fp_val, &ew, &sw, nullptr),
               "unexpected NULL argument");

  ASSERT_TRUE(cvc5_term_is_fp_value(fp_val));
  ASSERT_FALSE(cvc5_term_is_fp_pos_zero(fp_val));
  ASSERT_FALSE(cvc5_term_is_fp_neg_zero(fp_val));
  ASSERT_FALSE(cvc5_term_is_fp_pos_inf(fp_val));
  ASSERT_FALSE(cvc5_term_is_fp_neg_inf(fp_val));
  ASSERT_FALSE(cvc5_term_is_fp_nan(fp_val));

  cvc5_term_get_fp_value(fp_val, &ew, &sw, &res);
  ASSERT_EQ(ew, 5u);
  ASSERT_EQ(sw, 11u);
  ASSERT_TRUE(cvc5_term_is_equal(bv_val, res));

  ASSERT_TRUE(cvc5_term_is_fp_pos_zero(cvc5_mk_fp_pos_zero(d_tm, 5, 11)));
  ASSERT_TRUE(cvc5_term_is_fp_neg_zero(cvc5_mk_fp_neg_zero(d_tm, 5, 11)));
  ASSERT_TRUE(cvc5_term_is_fp_pos_inf(cvc5_mk_fp_pos_inf(d_tm, 5, 11)));
  ASSERT_TRUE(cvc5_term_is_fp_neg_inf(cvc5_mk_fp_neg_inf(d_tm, 5, 11)));
  ASSERT_TRUE(cvc5_term_is_fp_nan(cvc5_mk_fp_nan(d_tm, 5, 11)));
}

TEST_F(TestCApiBlackTerm, get_set_value)
{
  Cvc5Sort s = cvc5_mk_set_sort(d_tm, d_int);

  Cvc5Term i1 = cvc5_mk_integer_int64(d_tm, 5);
  Cvc5Term i2 = cvc5_mk_integer_int64(d_tm, 7);

  Cvc5Term s1 = cvc5_mk_empty_set(d_tm, s);
  std::vector<Cvc5Term> args = {i1};
  Cvc5Term s2 =
      cvc5_mk_term(d_tm, CVC5_KIND_SET_SINGLETON, args.size(), args.data());
  Cvc5Term s3 =
      cvc5_mk_term(d_tm, CVC5_KIND_SET_SINGLETON, args.size(), args.data());
  args = {i2};
  Cvc5Term s4 =
      cvc5_mk_term(d_tm, CVC5_KIND_SET_SINGLETON, args.size(), args.data());
  args = {s3, s4};
  args = {s2,
          cvc5_mk_term(d_tm, CVC5_KIND_SET_UNION, args.size(), args.data())};
  Cvc5Term s5 =
      cvc5_mk_term(d_tm, CVC5_KIND_SET_UNION, args.size(), args.data());

  ASSERT_DEATH(cvc5_term_is_set_value(nullptr), "invalid term");
  ASSERT_TRUE(cvc5_term_is_set_value(s1));
  ASSERT_TRUE(cvc5_term_is_set_value(s2));
  ASSERT_TRUE(cvc5_term_is_set_value(s3));
  ASSERT_TRUE(cvc5_term_is_set_value(s4));
  ASSERT_FALSE(cvc5_term_is_set_value(s5));
  s5 = cvc5_simplify(d_solver, s5, false);
  ASSERT_TRUE(cvc5_term_is_set_value(s5));

  size_t size;
  ASSERT_DEATH(cvc5_term_get_set_value(nullptr, &size), "invalid term");
  ASSERT_DEATH(cvc5_term_get_set_value(s1, nullptr),
               "unexpected NULL argument");
  (void)cvc5_term_get_set_value(s1, &size);
  ASSERT_EQ(size, 0);
  const Cvc5Term* res2 = cvc5_term_get_set_value(s2, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res2[0], i1));
  const Cvc5Term* res3 = cvc5_term_get_set_value(s3, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res3[0], i1));
  const Cvc5Term* res4 = cvc5_term_get_set_value(s4, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res4[0], i2));
  const Cvc5Term* res5 = cvc5_term_get_set_value(s5, &size);
  ASSERT_EQ(size, 2);
  ASSERT_TRUE(cvc5_term_is_equal(res5[0], i1));
  ASSERT_TRUE(cvc5_term_is_equal(res5[1], i2));
}

TEST_F(TestCApiBlackTerm, get_sequence_value)
{
  Cvc5Sort seq_sort = cvc5_mk_sequence_sort(d_tm, d_int);

  Cvc5Term i1 = cvc5_mk_integer_int64(d_tm, 5);
  Cvc5Term i2 = cvc5_mk_integer_int64(d_tm, 7);

  Cvc5Term s1 = cvc5_mk_empty_sequence(d_tm, seq_sort);
  std::vector<Cvc5Term> args = {i1};
  Cvc5Term s2 =
      cvc5_mk_term(d_tm, CVC5_KIND_SEQ_UNIT, args.size(), args.data());
  Cvc5Term s3 =
      cvc5_mk_term(d_tm, CVC5_KIND_SEQ_UNIT, args.size(), args.data());
  args = {i2};
  Cvc5Term s4 =
      cvc5_mk_term(d_tm, CVC5_KIND_SEQ_UNIT, args.size(), args.data());
  args = {s3, s4};
  args = {s2,
          cvc5_mk_term(d_tm, CVC5_KIND_SEQ_CONCAT, args.size(), args.data())};
  Cvc5Term s5 =
      cvc5_mk_term(d_tm, CVC5_KIND_SEQ_CONCAT, args.size(), args.data());

  ASSERT_DEATH(cvc5_mk_empty_sequence(nullptr, seq_sort),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_empty_sequence(d_tm, nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_term_is_sequence_value(nullptr), "invalid term");

  ASSERT_TRUE(cvc5_term_is_sequence_value(s1));
  ASSERT_FALSE(cvc5_term_is_sequence_value(s2));
  ASSERT_FALSE(cvc5_term_is_sequence_value(s3));
  ASSERT_FALSE(cvc5_term_is_sequence_value(s4));
  ASSERT_FALSE(cvc5_term_is_sequence_value(s5));
  s2 = cvc5_simplify(d_solver, s2, false);
  ASSERT_TRUE(cvc5_term_is_sequence_value(s2));
  s3 = cvc5_simplify(d_solver, s3, false);
  ASSERT_TRUE(cvc5_term_is_sequence_value(s3));
  s4 = cvc5_simplify(d_solver, s4, false);
  ASSERT_TRUE(cvc5_term_is_sequence_value(s4));
  s5 = cvc5_simplify(d_solver, s5, false);
  ASSERT_TRUE(cvc5_term_is_sequence_value(s5));

  size_t size;
  ASSERT_DEATH(cvc5_term_get_sequence_value(nullptr, &size), "invalid term");
  ASSERT_DEATH(cvc5_term_get_sequence_value(s1, nullptr),
               "unexpected NULL argument");
  (void)cvc5_term_get_sequence_value(s1, &size);
  ASSERT_EQ(size, 0);
  const Cvc5Term* res2 = cvc5_term_get_sequence_value(s2, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res2[0], i1));
  const Cvc5Term* res3 = cvc5_term_get_sequence_value(s3, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res3[0], i1));
  const Cvc5Term* res4 = cvc5_term_get_sequence_value(s4, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_term_is_equal(res4[0], i2));
  const Cvc5Term* res5 = cvc5_term_get_sequence_value(s5, &size);
  ASSERT_EQ(size, 3);
  ASSERT_TRUE(cvc5_term_is_equal(res5[0], i1));
  ASSERT_TRUE(cvc5_term_is_equal(res5[1], i1));
  ASSERT_TRUE(cvc5_term_is_equal(res5[2], i2));

  seq_sort = cvc5_mk_sequence_sort(d_tm, d_real);
  Cvc5Term s = cvc5_mk_empty_sequence(d_tm, seq_sort);
  ASSERT_EQ(cvc5_term_get_kind(s), CVC5_KIND_CONST_SEQUENCE);
  // empty sequence has zero elements
  (void)cvc5_term_get_sequence_value(s, &size);
  ASSERT_EQ(size, 0);

  // A seq.unit app is not a constant sequence (regardless of whether it is
  // applied to a constant).
  args = {cvc5_mk_real_int64(d_tm, 1)};
  Cvc5Term su =
      cvc5_mk_term(d_tm, CVC5_KIND_SEQ_UNIT, args.size(), args.data());
  ASSERT_DEATH(cvc5_term_get_sequence_value(su, &size), "invalid argument");
}

TEST_F(TestCApiBlackTerm, substitute)
{
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  std::vector<Cvc5Term> args = {x, x};
  Cvc5Term xpx = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {one, one};
  Cvc5Term onepone =
      cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());

  ASSERT_DEATH(cvc5_term_substitute_term(nullptr, x, one), "invalid term");
  ASSERT_DEATH(cvc5_term_substitute_term(xpx, nullptr, one), "invalid term");
  ASSERT_DEATH(cvc5_term_substitute_term(xpx, x, nullptr), "invalid term");

  ASSERT_TRUE(
      cvc5_term_is_equal(cvc5_term_substitute_term(xpx, x, one), onepone));
  // incorrect due to type
  ASSERT_DEATH(cvc5_term_substitute_term(xpx, one, ttrue),
               "expected terms of the same sort");

  // simultaneous substitution
  Cvc5Term y = cvc5_mk_const(d_tm, d_int, "y");
  args = {x, y};
  Cvc5Term xpy = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  args = {y, one};
  Cvc5Term xpone = cvc5_mk_term(d_tm, CVC5_KIND_ADD, args.size(), args.data());
  std::vector<Cvc5Term> es = {x, y};
  std::vector<Cvc5Term> rs = {y, one};
  ASSERT_EQ(cvc5_term_substitute_terms(xpy, es.size(), es.data(), rs.data()),
            xpone);

  // incorrect substitution due to types
  rs[1] = ttrue;
  ASSERT_DEATH(cvc5_term_substitute_terms(xpy, es.size(), es.data(), rs.data()),
               "expecting terms of the same sort at index 1");

  // null cannot substitute
  es = {nullptr, y};
  rs = {y, one};
  ASSERT_DEATH(cvc5_term_substitute_terms(xpy, es.size(), es.data(), rs.data()),
               "invalid term at index 0");
  es = {x, nullptr};
  ASSERT_DEATH(cvc5_term_substitute_terms(xpy, es.size(), es.data(), rs.data()),
               "invalid term at index 1");
  es = {x, y};
  rs = {nullptr, one};
  ASSERT_DEATH(cvc5_term_substitute_terms(xpy, es.size(), es.data(), rs.data()),
               "invalid term at index 0");
  rs = {y, nullptr};
  ASSERT_DEATH(cvc5_term_substitute_terms(xpy, es.size(), es.data(), rs.data()),
               "invalid term at index 1");
}

TEST_F(TestCApiBlackTerm, const_array)
{
  Cvc5Sort arr_sort = cvc5_mk_array_sort(d_tm, d_int, d_int);
  Cvc5Term a = cvc5_mk_const(d_tm, arr_sort, "a");
  Cvc5Term one = cvc5_mk_integer_int64(d_tm, 1);
  Cvc5Term two = cvc5_mk_bv_uint64(d_tm, 2, 2);
  Cvc5Term i = cvc5_mk_const(d_tm, d_int, "i");
  Cvc5Term const_arr = cvc5_mk_const_array(d_tm, arr_sort, one);

  ASSERT_DEATH(cvc5_mk_const_array(nullptr, arr_sort, one),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, nullptr, one), "invalid sort");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, arr_sort, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, arr_sort, two),
               "value does not match element sort");
  ASSERT_DEATH(cvc5_mk_const_array(d_tm, arr_sort, i), "invalid argument");

  ASSERT_DEATH(cvc5_term_get_const_array_base(nullptr), "invalid term");

  ASSERT_EQ(cvc5_term_get_kind(const_arr), CVC5_KIND_CONST_ARRAY);
  ASSERT_TRUE(
      cvc5_term_is_equal(cvc5_term_get_const_array_base(const_arr), one));
  ASSERT_DEATH(cvc5_term_get_const_array_base(a), "invalid argument");

  arr_sort = cvc5_mk_array_sort(d_tm, d_real, d_real);
  Cvc5Term zero_array =
      cvc5_mk_const_array(d_tm, arr_sort, cvc5_mk_real_int64(d_tm, 0));
  std::vector<Cvc5Term> args = {
      zero_array, cvc5_mk_real_int64(d_tm, 1), cvc5_mk_real_int64(d_tm, 2)};
  Cvc5Term stores =
      cvc5_mk_term(d_tm, CVC5_KIND_STORE, args.size(), args.data());
  args = {stores, cvc5_mk_real_int64(d_tm, 2), cvc5_mk_real_int64(d_tm, 3)};
  stores = cvc5_mk_term(d_tm, CVC5_KIND_STORE, args.size(), args.data());
  args = {stores, cvc5_mk_real_int64(d_tm, 4), cvc5_mk_real_int64(d_tm, 5)};
  stores = cvc5_mk_term(d_tm, CVC5_KIND_STORE, args.size(), args.data());
}

TEST_F(TestCApiBlackTerm, get_cardinality_constraint)
{
  ASSERT_DEATH(cvc5_mk_cardinality_constraint(nullptr, d_uninterpreted, 3),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_cardinality_constraint(d_tm, nullptr, 3),
               "invalid sort");
  ASSERT_DEATH(cvc5_term_is_cardinality_constraint(nullptr), "invalid term");

  Cvc5Term t = cvc5_mk_cardinality_constraint(d_tm, d_uninterpreted, 3);
  ASSERT_TRUE(cvc5_term_is_cardinality_constraint(t));

  Cvc5Sort res;
  uint32_t res_upper;
  ASSERT_DEATH(cvc5_term_get_cardinality_constraint(nullptr, &res, &res_upper),
               "invalid term");
  ASSERT_DEATH(cvc5_term_get_cardinality_constraint(t, nullptr, &res_upper),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_term_get_cardinality_constraint(t, &res, nullptr),
               "unexpected NULL argument");

  cvc5_term_get_cardinality_constraint(t, &res, &res_upper);
  ASSERT_TRUE(cvc5_sort_is_equal(res, d_uninterpreted));
  ASSERT_EQ(res_upper, 3);

  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  ASSERT_FALSE(cvc5_term_is_cardinality_constraint(x));
  ASSERT_DEATH(cvc5_term_get_cardinality_constraint(x, &res, &res_upper),
               "invalid argument");
}

TEST_F(TestCApiBlackTerm, get_real_algebraic_number)
{
  cvc5_set_option(d_solver, "produce-models", "true");
  cvc5_set_logic(d_solver, "QF_NRA");
  Cvc5Term x = cvc5_mk_const(d_tm, d_real, "x");
  Cvc5Term y = cvc5_mk_var(d_tm, d_real, "y");
  std::vector<Cvc5Term> args = {x, x};
  Cvc5Term x2 = cvc5_mk_term(d_tm, CVC5_KIND_MULT, args.size(), args.data());
  Cvc5Term two = cvc5_mk_real_num_den(d_tm, 2, 1);
  args = {x2, two};
  Cvc5Term eq = cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  cvc5_assert_formula(d_solver, eq);

  ASSERT_DEATH(cvc5_term_is_real_algebraic_number(nullptr), "invalid term");
  ASSERT_DEATH(
      cvc5_term_get_real_algebraic_number_defining_polynomial(nullptr, y),
      "invalid term");
  ASSERT_DEATH(
      cvc5_term_get_real_algebraic_number_defining_polynomial(x, nullptr),
      "invalid term");
  ASSERT_DEATH(cvc5_term_get_real_algebraic_number_lower_bound(nullptr),
               "invalid term");
  ASSERT_DEATH(cvc5_term_get_real_algebraic_number_upper_bound(nullptr),
               "invalid term");

  // Note that check-sat should only return "sat" if libpoly is enabled.
  // Otherwise, we do not test the following functionality.
  if (cvc5_result_is_sat(cvc5_check_sat(d_solver)))
  {
    // We find a model for (x*x = 2), where x should be a real algebraic number.
    // We assert that its defining polynomial is non-null and its lower and
    // upper bounds are real.
    Cvc5Term vx = cvc5_get_value(d_solver, x);
    ASSERT_TRUE(cvc5_term_is_real_algebraic_number(vx));
    Cvc5Term poly =
        cvc5_term_get_real_algebraic_number_defining_polynomial(vx, y);
    ASSERT_NE(poly, nullptr);

    Cvc5Term lb = cvc5_term_get_real_algebraic_number_lower_bound(vx);
    Cvc5Term ub = cvc5_term_get_real_algebraic_number_upper_bound(vx);
    ASSERT_TRUE(cvc5_term_is_real_value(lb));
    ASSERT_TRUE(cvc5_term_is_real_value(ub));
    // cannot call with non-variable
    Cvc5Term yc = cvc5_mk_const(d_tm, d_real, "y");
    ASSERT_DEATH(
        cvc5_term_get_real_algebraic_number_defining_polynomial(vx, yc),
        "invalid argument");
  }
}

TEST_F(TestCApiBlackTerm, get_skolem)
{
  size_t size;
  ASSERT_DEATH(cvc5_term_is_skolem(nullptr), "invalid term");
  ASSERT_DEATH(cvc5_term_get_skolem_id(nullptr), "invalid term");
  // ordinary variables are not skolems
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  ASSERT_FALSE(cvc5_term_is_skolem(x));
  ASSERT_DEATH(cvc5_term_get_skolem_id(x), "invalid argument");
  ASSERT_DEATH(cvc5_term_get_skolem_indices(x, &size), "invalid argument");
  ASSERT_DEATH(cvc5_term_get_skolem_indices(nullptr, &size), "invalid term");
  ASSERT_DEATH(cvc5_term_get_skolem_indices(x, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackTerm, term_scoped_to_string)
{
  Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
  ASSERT_EQ(cvc5_term_to_string(x), std::string("x"));
  ASSERT_EQ(cvc5_term_to_string(x), std::string("x"));
}

}  // namespace cvc5::internal::test
