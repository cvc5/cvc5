/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the lifetime guarantees of the C API.
 *
 * Objects created via the C API (sorts, ops, terms, datatypes, results,
 * proofs, grammars, ...) keep their term manager alive. They must therefore
 * remain usable after the term manager and/or solver that created them have
 * been deleted, until they are released.
 *
 * Mirrors test/unit/api/cpp/api_lifetime_black.cpp.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <string>
#include <vector>

#include "gtest/gtest.h"
#include "test_capi.h"

namespace cvc5::internal::test {

class TestCApiBlackLifetime : public ::testing::Test
{
};

TEST_F(TestCApiBlackLifetime, sortOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5Sort s = cvc5_get_integer_sort(tm);
  Cvc5Sort b = cvc5_get_boolean_sort(tm);
  Cvc5Sort arr = cvc5_mk_array_sort(tm, s, b);
  cvc5_sort_release(b);
  cvc5_term_manager_delete(tm);
  // tm is deleted here; s and arr must still be usable.
  ASSERT_TRUE(cvc5_sort_is_integer(s));
  ASSERT_TRUE(cvc5_sort_is_array(arr));
  Cvc5Sort idx = cvc5_sort_array_get_index_sort(arr);
  ASSERT_TRUE(cvc5_sort_is_equal(idx, s));
  ASSERT_EQ(std::string(cvc5_sort_to_string(s)), "Int");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_sort_release(idx);
  cvc5_sort_release(arr);
  cvc5_sort_release(s);
}

TEST_F(TestCApiBlackLifetime, termOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5Sort s = cvc5_get_integer_sort(tm);
  Cvc5Term x = cvc5_mk_const(tm, s, "x");
  Cvc5Term one = cvc5_mk_integer_int64(tm, 1);
  Cvc5Term args[2] = {x, one};
  Cvc5Term t = cvc5_mk_term(tm, CVC5_KIND_ADD, 2, args);
  cvc5_term_release(x);
  cvc5_term_release(one);
  cvc5_term_manager_delete(tm);
  // tm is deleted here; t must still be usable, including API functions that
  // create new objects (children, sorts) from it.
  ASSERT_EQ(cvc5_term_get_kind(t), CVC5_KIND_ADD);
  ASSERT_EQ(cvc5_term_get_num_children(t), 2);
  Cvc5Sort ts = cvc5_term_get_sort(t);
  ASSERT_TRUE(cvc5_sort_is_equal(ts, s));
  Cvc5Term child = cvc5_term_get_child(t, 0);
  ASSERT_EQ(std::string(cvc5_term_to_string(child)), "x");
  ASSERT_EQ(std::string(cvc5_term_to_string(t)), "(+ x 1)");
  ASSERT_TRUE(cvc5_term_is_equal(t, t));
  ASSERT_FALSE(cvc5_has_error());
  cvc5_term_release(child);
  cvc5_sort_release(ts);
  cvc5_sort_release(s);
  cvc5_term_release(t);
}

TEST_F(TestCApiBlackLifetime, termOutlivesTermManagerReleaseAll)
{
  // Releasing all managed objects after the term manager has been deleted
  // must free the term manager.
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5Term t = cvc5_mk_true(tm);
  Cvc5Term f = cvc5_mk_false(tm);
  cvc5_term_manager_delete(tm);
  ASSERT_EQ(std::string(cvc5_term_to_string(t)), "true");
  ASSERT_EQ(std::string(cvc5_term_to_string(f)), "false");
  cvc5_term_manager_release(tm);
  ASSERT_FALSE(cvc5_has_error());
}

TEST_F(TestCApiBlackLifetime, termCopyOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5Term t = cvc5_mk_true(tm);
  Cvc5Term t2 = cvc5_term_copy(t);
  ASSERT_EQ(t, t2);
  cvc5_term_manager_delete(tm);
  // Both references must be released before the term is freed.
  cvc5_term_release(t);
  ASSERT_EQ(std::string(cvc5_term_to_string(t2)), "true");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_term_release(t2);
}

TEST_F(TestCApiBlackLifetime, opOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  uint32_t idxs[2] = {4, 0};
  Cvc5Op op = cvc5_mk_op(tm, CVC5_KIND_BITVECTOR_EXTRACT, 2, idxs);
  cvc5_term_manager_delete(tm);
  // tm is deleted here; op must still be usable.
  ASSERT_TRUE(cvc5_op_is_indexed(op));
  ASSERT_EQ(cvc5_op_get_kind(op), CVC5_KIND_BITVECTOR_EXTRACT);
  ASSERT_EQ(cvc5_op_get_num_indices(op), 2);
  Cvc5Term idx = cvc5_op_get_index(op, 0);
  ASSERT_EQ(std::string(cvc5_term_to_string(idx)), "4");
  ASSERT_EQ(std::string(cvc5_op_to_string(op)), "(_ extract 4 0)");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_term_release(idx);
  cvc5_op_release(op);
}

TEST_F(TestCApiBlackLifetime, datatypeOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(tm, "cons");
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  cvc5_dt_cons_decl_add_selector(cons, "head", int_sort);
  cvc5_sort_release(int_sort);
  cvc5_dt_cons_decl_add_selector_self(cons, "tail");
  cvc5_dt_decl_add_constructor(decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);
  Cvc5Sort list_sort = cvc5_mk_dt_sort(tm, decl);
  cvc5_term_manager_delete(tm);
  // tm is deleted here; the datatype, its constructors and selectors must
  // still be usable.
  Cvc5Datatype dt = cvc5_sort_get_datatype(list_sort);
  ASSERT_EQ(std::string(cvc5_dt_get_name(dt)), "list");
  ASSERT_EQ(cvc5_dt_get_num_constructors(dt), 2);
  for (size_t i = 0; i < 2; ++i)
  {
    Cvc5DatatypeConstructor c = cvc5_dt_get_constructor(dt, i);
    ASSERT_FALSE(std::string(cvc5_dt_cons_get_name(c)).empty());
    for (size_t j = 0, n = cvc5_dt_cons_get_num_selectors(c); j < n; ++j)
    {
      Cvc5DatatypeSelector sel = cvc5_dt_cons_get_selector(c, j);
      ASSERT_FALSE(std::string(cvc5_dt_sel_get_name(sel)).empty());
      cvc5_dt_sel_release(sel);
    }
    cvc5_dt_cons_release(c);
  }
  Cvc5DatatypeConstructor cons_ctor =
      cvc5_dt_get_constructor_by_name(dt, "cons");
  ASSERT_EQ(std::string(cvc5_dt_cons_get_name(cons_ctor)), "cons");
  Cvc5DatatypeSelector head =
      cvc5_dt_cons_get_selector_by_name(cons_ctor, "head");
  ASSERT_EQ(std::string(cvc5_dt_sel_get_name(head)), "head");
  Cvc5Sort head_sort = cvc5_dt_sel_get_codomain_sort(head);
  ASSERT_TRUE(cvc5_sort_is_integer(head_sort));
  ASSERT_FALSE(cvc5_has_error());
  cvc5_sort_release(head_sort);
  cvc5_dt_sel_release(head);
  cvc5_dt_cons_release(cons_ctor);
  cvc5_dt_release(dt);
  cvc5_sort_release(list_sort);
  cvc5_dt_cons_decl_release(nil);
  cvc5_dt_cons_decl_release(cons);
  cvc5_dt_decl_release(decl);
}

TEST_F(TestCApiBlackLifetime, solverOutlivesTermManager)
{
  // The solver keeps the term manager alive, so it (and the term manager
  // returned by cvc5_get_tm()) stays usable after the term manager has been
  // deleted.
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_term_manager_delete(tm);
  Cvc5TermManager* tm2 = cvc5_get_tm(slv);
  Cvc5Sort b = cvc5_get_boolean_sort(tm2);
  Cvc5Term x = cvc5_mk_const(tm2, b, "x");
  cvc5_assert_formula(slv, x);
  Cvc5Result res = cvc5_check_sat(slv);
  ASSERT_TRUE(cvc5_result_is_sat(res));
  ASSERT_FALSE(cvc5_has_error());
  cvc5_result_release(res);
  cvc5_term_release(x);
  cvc5_sort_release(b);
  cvc5_delete(slv);
}

TEST_F(TestCApiBlackLifetime, resultOutlivesSolverWhenCopied)
{
  // A result is released together with the solver that created it, but the
  // user can keep it alive by holding a reference to it. It then outlives
  // both the solver and the term manager: as in the C++ API, `cvc5::Result`
  // references neither of them.
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  Cvc5Result res = cvc5_result_copy(cvc5_check_sat(slv));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  ASSERT_TRUE(cvc5_result_is_sat(res));
  ASSERT_EQ(std::string(cvc5_result_to_string(res)), "sat");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_result_release(res);
}

TEST_F(TestCApiBlackLifetime, resultReleasedWithSolver)
{
  // Without such a reference, a result is freed together with the solver
  // (the leak checker would flag it otherwise).
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  (void)cvc5_check_sat(slv);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  ASSERT_FALSE(cvc5_has_error());
}

TEST_F(TestCApiBlackLifetime, deleteSolverBeforeTermManager)
{
  // Deleting solver and term manager in the usual order, with objects
  // outstanding that are released afterwards.
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  Cvc5Term t = cvc5_mk_true(tm);
  cvc5_assert_formula(slv, t);
  // keep a reference so that the result outlives the solver
  Cvc5Result res = cvc5_result_copy(cvc5_check_sat(slv));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  ASSERT_TRUE(cvc5_result_is_sat(res));
  ASSERT_EQ(std::string(cvc5_term_to_string(t)), "true");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_term_release(t);
  cvc5_result_release(res);
}

TEST_F(TestCApiBlackLifetime, valueOutlivesSolverAndTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-models", "true");
  Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
  Cvc5Term x = cvc5_mk_const(tm, int_sort, "x");
  Cvc5Term zero = cvc5_mk_integer_int64(tm, 0);
  Cvc5Term args[2] = {x, zero};
  Cvc5Term gt = cvc5_mk_term(tm, CVC5_KIND_GT, 2, args);
  cvc5_assert_formula(slv, gt);
  Cvc5Result res = cvc5_check_sat(slv);
  ASSERT_TRUE(cvc5_result_is_sat(res));
  Cvc5Term value = cvc5_get_value(slv, x);
  cvc5_result_release(res);
  cvc5_term_release(gt);
  cvc5_term_release(zero);
  cvc5_term_release(x);
  cvc5_sort_release(int_sort);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // Both the solver and the term manager are deleted here; the value term
  // obtained from the solver must still be usable.
  Cvc5Sort vs = cvc5_term_get_sort(value);
  ASSERT_TRUE(cvc5_sort_is_integer(vs));
  ASSERT_FALSE(std::string(cvc5_term_to_string(value)).empty());
  ASSERT_FALSE(cvc5_has_error());
  cvc5_sort_release(vs);
  cvc5_term_release(value);
}

TEST_F(TestCApiBlackLifetime, grammarOutlivesSolverAndTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "sygus", "true");
  Cvc5Sort b = cvc5_get_boolean_sort(tm);
  Cvc5Term start = cvc5_mk_var(tm, b, "start");
  Cvc5Term f = cvc5_mk_boolean(tm, false);
  Cvc5Term symbols[1] = {start};
  // keep a reference so that the grammar outlives the solver
  Cvc5Grammar g =
      cvc5_grammar_copy(cvc5_mk_grammar(slv, 0, nullptr, 1, symbols));
  cvc5_grammar_add_rule(g, start, f);
  cvc5_term_release(f);
  cvc5_term_release(start);
  cvc5_sort_release(b);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // Both the solver and the term manager are deleted here; the grammar must
  // still be usable.
  ASSERT_FALSE(std::string(cvc5_grammar_to_string(g)).empty());
  ASSERT_FALSE(cvc5_has_error());
  cvc5_grammar_release(g);
}

TEST_F(TestCApiBlackLifetime, proofOutlivesSolverAndTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  cvc5_set_option(slv, "produce-proofs", "true");
  Cvc5Sort b = cvc5_get_boolean_sort(tm);
  Cvc5Term x = cvc5_mk_const(tm, b, "x");
  Cvc5Term args[1] = {x};
  Cvc5Term not_x = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args);
  cvc5_assert_formula(slv, x);
  cvc5_assert_formula(slv, not_x);
  Cvc5Result res = cvc5_check_sat(slv);
  ASSERT_TRUE(cvc5_result_is_unsat(res));
  size_t size;
  const Cvc5Proof* proofs =
      cvc5_get_proof(slv, CVC5_PROOF_COMPONENT_FULL, &size);
  ASSERT_GT(size, 0);
  // keep a reference so that the proof outlives the solver
  Cvc5Proof proof = cvc5_proof_copy(proofs[0]);
  cvc5_result_release(res);
  cvc5_term_release(not_x);
  cvc5_term_release(x);
  cvc5_sort_release(b);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // Both the solver and the term manager are deleted here; the proof must
  // still be usable, including functions that create new objects from it.
  (void)cvc5_proof_get_rule(proof);
  Cvc5Term result = cvc5_proof_get_result(proof);
  ASSERT_FALSE(std::string(cvc5_term_to_string(result)).empty());
  size_t nchildren;
  const Cvc5Proof* children = cvc5_proof_get_children(proof, &nchildren);
  ASSERT_FALSE(cvc5_has_error());
  for (size_t i = 0; i < nchildren; ++i)
  {
    cvc5_proof_release(children[i]);
  }
  cvc5_term_release(result);
  cvc5_proof_release(proof);
}

TEST_F(TestCApiBlackLifetime, statisticsOutliveSolverAndTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  Cvc5Result res = cvc5_check_sat(slv);
  cvc5_result_release(res);
  Cvc5Statistics stats = cvc5_get_statistics(slv);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // Both the solver and the term manager are deleted here; the statistics
  // object must still be usable, including iterating over it (which creates
  // new statistic objects).
  ASSERT_FALSE(std::string(cvc5_stats_to_string(stats)).empty());
  std::vector<Cvc5Stat> handles;
  cvc5_stats_iter_init(stats, true, true);
  while (cvc5_stats_iter_has_next(stats))
  {
    handles.push_back(cvc5_stats_iter_next(stats, nullptr));
  }
  ASSERT_FALSE(handles.empty());
  cvc5_stats_release(stats);
  // the statistic objects keep the term manager alive on their own
  for (Cvc5Stat stat : handles)
  {
    (void)cvc5_stat_to_string(stat);
    ASSERT_FALSE(cvc5_has_error());
    cvc5_stat_release(stat);
  }
  ASSERT_FALSE(cvc5_has_error());
}

TEST_F(TestCApiBlackLifetime, statisticsCopyOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5Statistics stats = cvc5_term_manager_get_statistics(tm);
  Cvc5Statistics stats2 = cvc5_stats_copy(stats);
  ASSERT_EQ(stats, stats2);
  cvc5_term_manager_delete(tm);
  cvc5_stats_release(stats);
  // the second reference must still keep the term manager alive
  ASSERT_FALSE(std::string(cvc5_stats_to_string(stats2)).empty());
  ASSERT_FALSE(cvc5_has_error());
  cvc5_stats_release(stats2);
}

}  // namespace cvc5::internal::test
