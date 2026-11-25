/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the reference counts of C API objects.
 *
 * Copying a C API object increments its 32-bit reference count. The copy
 * functions must report an error instead of letting the count wrap around,
 * which would free the object while handles to it are still live (issue
 * #13211). Reaching the limit through the API takes 2^32 calls, so these tests
 * set the counts directly.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <cstdint>
#include <limits>
#include <vector>

#include "api/c/cvc5_c_structs.h"
#include "gtest/gtest.h"
#include "test_capi.h"

namespace cvc5::internal::test {

class TestCApiWhiteRefCount : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }

  /**
   * Check that copying `obj` succeeds until its reference count reaches its
   * maximum, and raises an error without changing the count afterwards.
   * Resets the reference count to one and releases `obj` at the end.
   */
  template <typename T>
  void check_copy_limit(T obj, T (*copy)(T), void (*release)(T))
  {
    ASSERT_NE(obj, nullptr);
    obj->d_refs = s_max - 1;
    ASSERT_EQ(copy(obj), obj);
    ASSERT_FALSE(cvc5_has_error());
    ASSERT_EQ(obj->d_refs, s_max);
    ASSERT_CVC5_ERROR(copy(obj), "reference count overflow");
    ASSERT_EQ(obj->d_refs, s_max);
    ASSERT_EQ(copy(obj), nullptr);
    ASSERT_EQ(obj->d_refs, s_max);
    obj->d_refs = 1;
    release(obj);
    ASSERT_FALSE(cvc5_has_error());
  }

  static constexpr uint32_t s_max = std::numeric_limits<uint32_t>::max();

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
};

TEST_F(TestCApiWhiteRefCount, sort)
{
  check_copy_limit(
      cvc5_get_integer_sort(d_tm), cvc5_sort_copy, cvc5_sort_release);
}

TEST_F(TestCApiWhiteRefCount, term)
{
  check_copy_limit(cvc5_mk_true(d_tm), cvc5_term_copy, cvc5_term_release);
}

TEST_F(TestCApiWhiteRefCount, op)
{
  std::vector<uint32_t> idxs = {4, 0};
  check_copy_limit(
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data()),
      cvc5_op_copy,
      cvc5_op_release);
}

TEST_F(TestCApiWhiteRefCount, datatype)
{
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(d_tm));
  cvc5_dt_decl_add_constructor(decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);
  Cvc5Sort sort = cvc5_mk_dt_sort(d_tm, decl);
  Cvc5Datatype dt = cvc5_sort_get_datatype(sort);
  ASSERT_FALSE(cvc5_has_error());

  check_copy_limit(cons, cvc5_dt_cons_decl_copy, cvc5_dt_cons_decl_release);
  check_copy_limit(decl, cvc5_dt_decl_copy, cvc5_dt_decl_release);
  check_copy_limit(
      cvc5_dt_get_constructor(dt, 0), cvc5_dt_cons_copy, cvc5_dt_cons_release);
  check_copy_limit(
      cvc5_dt_get_selector(dt, "head"), cvc5_dt_sel_copy, cvc5_dt_sel_release);
  check_copy_limit(dt, cvc5_dt_copy, cvc5_dt_release);
}

TEST_F(TestCApiWhiteRefCount, statistics)
{
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  check_copy_limit(cvc5_stats_get(stats, "global::totalTime"),
                   cvc5_stat_copy,
                   cvc5_stat_release);
  check_copy_limit(stats, cvc5_stats_copy, cvc5_stats_release);
}

TEST_F(TestCApiWhiteRefCount, grammar)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Sort bool_sort = cvc5_get_boolean_sort(d_tm);
  Cvc5Term start = cvc5_mk_var(d_tm, bool_sort, "start");
  Cvc5Term x = cvc5_mk_var(d_tm, bool_sort, "x");
  check_copy_limit(cvc5_mk_grammar(d_tm, 1, &x, 1, &start),
                   cvc5_grammar_copy,
                   cvc5_grammar_release);
}

TEST_F(TestCApiWhiteRefCount, result)
{
  check_copy_limit(
      cvc5_check_sat(d_solver), cvc5_result_copy, cvc5_result_release);
}

TEST_F(TestCApiWhiteRefCount, synth_result)
{
  cvc5_set_option(d_solver, "sygus", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, cvc5_get_boolean_sort(d_tm));
  cvc5_add_sygus_constraint(d_solver, cvc5_mk_true(d_tm));
  check_copy_limit(cvc5_check_synth(d_solver),
                   cvc5_synth_result_copy,
                   cvc5_synth_result_release);
}

TEST_F(TestCApiWhiteRefCount, proof)
{
  cvc5_set_option(d_solver, "produce-proofs", "true");
  cvc5_assert_formula(d_solver, cvc5_mk_false(d_tm));
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(d_solver)));
  size_t size;
  const Cvc5Proof* proofs =
      cvc5_get_proof(d_solver, CVC5_PROOF_COMPONENT_FULL, &size);
  ASSERT_EQ(size, 1);
  check_copy_limit(proofs[0], cvc5_proof_copy, cvc5_proof_release);
}

TEST_F(TestCApiWhiteRefCount, export_existing)
{
  // Objects that are already exported are handed out again with an
  // incremented reference count, which must not wrap around either.
  Cvc5Term t = cvc5_mk_true(d_tm);
  t->d_refs = s_max;
  ASSERT_CVC5_ERROR(cvc5_mk_true(d_tm), "reference count overflow");
  ASSERT_EQ(t->d_refs, s_max);
  Cvc5Sort s = cvc5_get_integer_sort(d_tm);
  s->d_refs = s_max;
  ASSERT_CVC5_ERROR(cvc5_get_integer_sort(d_tm), "reference count overflow");
  ASSERT_EQ(s->d_refs, s_max);
  t->d_refs = 1;
  cvc5_term_release(t);
  s->d_refs = 1;
  cvc5_sort_release(s);
}

}  // namespace cvc5::internal::test
