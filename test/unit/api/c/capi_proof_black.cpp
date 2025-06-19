/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of proof-related functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/check.h"
#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackProof : public ::testing::Test
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

  Cvc5Proof create_proof()
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
    Cvc5Result res = cvc5_check_sat(d_solver);
    Assert(cvc5_result_is_unsat(res));
    size_t size;
    const Cvc5Proof* proofs =
        cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &size);
    Assert(size == 1);
    return proofs[0];
  }

  Cvc5Proof create_rewrite_proof()
  {
    cvc5_set_option(d_solver, "produce-proofs", "true");
    cvc5_set_option(d_solver, "proof-granularity", "dsl-rewrite");
    Cvc5Term x = cvc5_mk_const(d_tm, d_int, "x");
    Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 2);
    std::vector<Cvc5Term> args = {x, zero};
    Cvc5Term geq =
        cvc5_mk_term(d_tm, CVC5_KIND_GEQ, args.size(), args.data());
    args = {zero, x};
    Cvc5Term leq =
        cvc5_mk_term(d_tm, CVC5_KIND_LEQ, args.size(), args.data());
    args = {geq, leq};
    cvc5_assert_formula(
        d_solver,
        cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data()));
    Cvc5Result res = cvc5_check_sat(d_solver);
    Assert(cvc5_result_is_unsat(res));
    size_t size;
    const Cvc5Proof* proofs =
        cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &size);
    Assert(size == 1);
    return proofs[0];
  }

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5Sort d_bool;
  Cvc5Sort d_int;
  Cvc5Sort d_real;
  Cvc5Sort d_str;
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackProof, get_rule)
{
  ASSERT_DEATH(cvc5_proof_get_rule(nullptr), "invalid proof");
  Cvc5Proof proof = create_proof();
  ASSERT_EQ(cvc5_proof_get_rule(proof), CVC5_PROOF_RULE_SCOPE);
}

TEST_F(TestCApiBlackProof, get_rewrite_rule)
{
  ASSERT_DEATH(cvc5_proof_get_rewrite_rule(nullptr), "invalid proof");

  Cvc5Proof proof = create_rewrite_proof();
  ASSERT_DEATH(cvc5_proof_get_rewrite_rule(proof), "to return `DSL_REWRITE`");
  Cvc5ProofRule rule;
  std::vector<Cvc5Proof> stack = {proof};
  do
  {
    proof = stack.back();
    stack.pop_back();
    rule = cvc5_proof_get_rule(proof);
    size_t size;
    const Cvc5Proof* children = cvc5_proof_get_children(proof, &size);
    for (size_t i = 0; i < size; ++i)
    {
      stack.push_back(children[i]);
    }
  } while (rule != CVC5_PROOF_RULE_DSL_REWRITE);
  (void)cvc5_proof_get_rewrite_rule(proof);
}

TEST_F(TestCApiBlackProof, get_result)
{
  ASSERT_DEATH(cvc5_proof_get_result(nullptr), "invalid proof");
  Cvc5Proof proof = create_proof();
  (void)cvc5_proof_get_result(proof);
}

TEST_F(TestCApiBlackProof, get_children)
{
  Cvc5Proof proof = create_proof();
  size_t size;
  (void)cvc5_proof_get_children(proof, &size);
  ASSERT_TRUE(size > 0);
  ASSERT_DEATH(cvc5_proof_get_children(nullptr, &size), "invalid proof");
  ASSERT_DEATH(cvc5_proof_get_children(proof, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackProof, get_arguments)
{
  Cvc5Proof proof = create_proof();
  size_t size;
  (void)cvc5_proof_get_arguments(proof, &size);
  ASSERT_DEATH(cvc5_proof_get_arguments(nullptr, &size), "invalid proof");
  ASSERT_DEATH(cvc5_proof_get_arguments(proof, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackProof, is_equal_disequal_hash)
{
  Cvc5Proof proof = create_proof();
  size_t size;
  Cvc5Proof x = cvc5_proof_get_children(proof, &size)[0];
  Cvc5Proof y = cvc5_proof_get_children(x, &size)[0];

  ASSERT_TRUE(cvc5_proof_is_equal(x, x));
  ASSERT_FALSE(cvc5_proof_is_disequal(x, x));
  ASSERT_FALSE(cvc5_proof_is_equal(x, y));
  ASSERT_TRUE(cvc5_proof_is_disequal(x, y));
  ASSERT_TRUE(cvc5_proof_is_equal(nullptr, nullptr));
  ASSERT_FALSE(cvc5_proof_is_equal(x, nullptr));
  ASSERT_FALSE(cvc5_proof_is_equal(nullptr, y));
  ASSERT_TRUE(cvc5_proof_is_disequal(x, nullptr));
  ASSERT_TRUE(cvc5_proof_is_disequal(nullptr, y));

  ASSERT_EQ(cvc5_proof_hash(x), cvc5_proof_hash(x));
  ASSERT_NE(cvc5_proof_hash(x), cvc5_proof_hash(y));
  ASSERT_DEATH(cvc5_proof_hash(nullptr), "invalid proof");
}

TEST_F(TestCApiBlackProof, copy_release)
{
  ASSERT_DEATH(cvc5_proof_copy(nullptr), "invalid proof");
  ASSERT_DEATH(cvc5_proof_release(nullptr), "invalid proof");
  Cvc5Proof proof = create_proof();
  ASSERT_EQ(cvc5_proof_get_rule(proof), CVC5_PROOF_RULE_SCOPE);
  Cvc5Proof proof2 = cvc5_proof_copy(proof);
  ASSERT_EQ(cvc5_proof_get_rule(proof), CVC5_PROOF_RULE_SCOPE);
  ASSERT_EQ(cvc5_proof_get_rule(proof2), CVC5_PROOF_RULE_SCOPE);
  ASSERT_TRUE(cvc5_proof_is_equal(proof, proof2));
  cvc5_proof_release(proof);
  ASSERT_EQ(cvc5_proof_get_rule(proof), CVC5_PROOF_RULE_SCOPE);
  ASSERT_EQ(cvc5_proof_get_rule(proof2), CVC5_PROOF_RULE_SCOPE);
  cvc5_proof_release(proof);
  // we cannot reliably check that querying on the (now freed) proof fails
  // unless ASAN is enabled
}
}  // namespace cvc5::internal::test
