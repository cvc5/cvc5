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
 * Black box testing of the guards of the C API functions.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackSort : public ::testing::Test
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

  Cvc5Sort create_datatype_sort()
  {
    Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
    Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
    cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(d_tm));
    cvc5_dt_cons_decl_add_selector_self(cons, "tail");
    cvc5_dt_decl_add_constructor(decl, cons);
    Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
    cvc5_dt_decl_add_constructor(decl, nil);
    return cvc5_mk_dt_sort(d_tm, decl);
  }

  Cvc5Sort create_param_datatype_sort()
  {
    std::vector<Cvc5Sort> sorts = {cvc5_mk_param_sort(d_tm, "T")};
    Cvc5DatatypeDecl decl =
        cvc5_mk_dt_decl_with_params(d_tm, "paramlist", 1, sorts.data(), false);
    Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
    cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(d_tm));
    cvc5_dt_decl_add_constructor(decl, cons);
    Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
    cvc5_dt_decl_add_constructor(decl, nil);
    return cvc5_mk_dt_sort(d_tm, decl);
  }

  Cvc5TermManager* d_tm;
  Cvc5Sort d_bool;
  Cvc5Sort d_int;
  Cvc5Sort d_real;
};

TEST_F(TestCApiBlackSort, hash)
{
  ASSERT_DEATH(cvc5_sort_hash(nullptr), "invalid sort");
  (void)cvc5_sort_hash(d_int);
  ASSERT_EQ(cvc5_sort_hash(d_int), cvc5_sort_hash(d_int));
  ASSERT_NE(cvc5_sort_hash(d_int), cvc5_sort_hash(d_bool));
}

TEST_F(TestCApiBlackSort, copy_release)
{
  ASSERT_DEATH(cvc5_sort_copy(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_release(nullptr), "invalid sort");
  size_t hash1 = cvc5_sort_hash(d_int);
  Cvc5Sort int_copy = cvc5_sort_copy(d_int);
  size_t hash2 = cvc5_sort_hash(int_copy);
  ASSERT_EQ(hash1, hash2);
  cvc5_sort_release(d_int);
  ASSERT_EQ(hash1, cvc5_sort_hash(d_int));
  cvc5_sort_release(d_int);
  // we cannot reliably check that querying on the (now freed) sort fails
  // unless ASAN is enabled
}

TEST_F(TestCApiBlackSort, compare)
{
  ASSERT_DEATH(cvc5_sort_compare(d_int, nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_compare(nullptr, d_int), "invalid sort");
  ASSERT_TRUE(cvc5_sort_is_equal(d_int, d_int));
  ASSERT_TRUE(cvc5_sort_is_disequal(d_int, d_bool));
  ASSERT_FALSE(cvc5_sort_is_equal(d_int, nullptr));
  ASSERT_TRUE(cvc5_sort_is_disequal(d_int, nullptr));
  ASSERT_EQ(cvc5_sort_compare(d_int, d_int), 0);
}

TEST_F(TestCApiBlackSort, get_kind)
{
  ASSERT_DEATH(cvc5_sort_get_kind(nullptr), "invalid sort");
  ASSERT_EQ(cvc5_sort_get_kind(d_bool), CVC5_SORT_KIND_BOOLEAN_SORT);
  Cvc5Sort dt_sort = create_datatype_sort();
  ASSERT_EQ(cvc5_sort_get_kind(dt_sort), CVC5_SORT_KIND_DATATYPE_SORT);
  Cvc5Sort arr_sort = cvc5_mk_array_sort(d_tm, d_real, d_int);
  ASSERT_EQ(cvc5_sort_get_kind(arr_sort), CVC5_SORT_KIND_ARRAY_SORT);
  Cvc5Sort fp_sort = cvc5_mk_fp_sort(d_tm, 8, 24);
  ASSERT_EQ(cvc5_sort_get_kind(fp_sort), CVC5_SORT_KIND_FLOATINGPOINT_SORT);
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 8);
  ASSERT_EQ(cvc5_sort_get_kind(bv_sort), CVC5_SORT_KIND_BITVECTOR_SORT);
  Cvc5Sort abs_sort =
      cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_BITVECTOR_SORT);
  ASSERT_EQ(cvc5_sort_get_kind(abs_sort), CVC5_SORT_KIND_ABSTRACT_SORT);
}

TEST_F(TestCApiBlackSort, has_get_symbol)
{
  Cvc5Sort s0 = cvc5_mk_param_sort(d_tm, "s0");
  Cvc5Sort s1 = cvc5_mk_param_sort(d_tm, "|s1\\|");

  ASSERT_FALSE(cvc5_sort_has_symbol(nullptr));
  ASSERT_FALSE(cvc5_sort_has_symbol(d_bool));
  ASSERT_TRUE(cvc5_sort_has_symbol(s0));
  ASSERT_TRUE(cvc5_sort_has_symbol(s1));

  ASSERT_DEATH(cvc5_sort_get_symbol(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_get_symbol(d_bool), "has no symbol");
  ASSERT_EQ(cvc5_sort_get_symbol(s0), std::string("s0"));
  ASSERT_EQ(cvc5_sort_get_symbol(s1), std::string("|s1\\|"));
}

TEST_F(TestCApiBlackSort, is_boolean)
{
  ASSERT_FALSE(cvc5_sort_is_boolean(nullptr));
  ASSERT_TRUE(cvc5_sort_is_boolean(d_bool));
}

TEST_F(TestCApiBlackSort, is_integer)
{
  ASSERT_FALSE(cvc5_sort_is_integer(nullptr));
  ASSERT_TRUE(cvc5_sort_is_integer(d_int));
  ASSERT_FALSE(cvc5_sort_is_integer(d_real));
}

TEST_F(TestCApiBlackSort, is_real)
{
  ASSERT_FALSE(cvc5_sort_is_real(nullptr));
  ASSERT_TRUE(cvc5_sort_is_real(d_real));
  ASSERT_FALSE(cvc5_sort_is_real(d_int));
}

TEST_F(TestCApiBlackSort, is_string)
{
  ASSERT_FALSE(cvc5_sort_is_string(nullptr));
  ASSERT_TRUE(cvc5_sort_is_string(cvc5_get_string_sort(d_tm)));
  ASSERT_FALSE(cvc5_sort_is_string(d_int));
}

TEST_F(TestCApiBlackSort, is_regexp)
{
  ASSERT_FALSE(cvc5_sort_is_regexp(nullptr));
  ASSERT_TRUE(cvc5_sort_is_regexp(cvc5_get_regexp_sort(d_tm)));
  ASSERT_FALSE(cvc5_sort_is_regexp(d_int));
}

TEST_F(TestCApiBlackSort, is_rm)
{
  ASSERT_FALSE(cvc5_sort_is_rm(nullptr));
  ASSERT_TRUE(cvc5_sort_is_rm(cvc5_get_rm_sort(d_tm)));
  ASSERT_FALSE(cvc5_sort_is_rm(d_int));
}

TEST_F(TestCApiBlackSort, is_bv)
{
  ASSERT_FALSE(cvc5_sort_is_bv(nullptr));
  ASSERT_TRUE(cvc5_sort_is_bv(cvc5_mk_bv_sort(d_tm, 8)));
  ASSERT_FALSE(cvc5_sort_is_bv(d_int));
}

TEST_F(TestCApiBlackSort, is_ff)
{
  ASSERT_FALSE(cvc5_sort_is_ff(nullptr));
  ASSERT_TRUE(cvc5_sort_is_ff(cvc5_mk_ff_sort(d_tm, "7", 10)));
  ASSERT_FALSE(cvc5_sort_is_ff(d_int));
}

TEST_F(TestCApiBlackSort, is_fp)
{
  ASSERT_FALSE(cvc5_sort_is_fp(nullptr));
  ASSERT_TRUE(cvc5_sort_is_fp(cvc5_mk_fp_sort(d_tm, 8, 24)));
  ASSERT_FALSE(cvc5_sort_is_fp(d_int));
}

TEST_F(TestCApiBlackSort, is_dt)
{
  Cvc5Sort dt_sort = create_datatype_sort();
  ASSERT_FALSE(cvc5_sort_is_dt(nullptr));
  ASSERT_TRUE(cvc5_sort_is_dt(dt_sort));
  ASSERT_FALSE(cvc5_sort_is_dt(d_int));
}

TEST_F(TestCApiBlackSort, is_dt_constructor)
{
  Cvc5Sort dt_sort = create_datatype_sort();
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sort);
  ASSERT_DEATH(cvc5_dt_get_constructor(dt, 3), "index out of bounds");
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  Cvc5Sort cons_sort = cvc5_term_get_sort(cvc5_dt_cons_get_term(cons));
  ASSERT_FALSE(cvc5_sort_is_dt(nullptr));
  ASSERT_TRUE(cvc5_sort_is_dt_constructor(cons_sort));
  ASSERT_FALSE(cvc5_sort_is_dt_constructor(d_int));
}

TEST_F(TestCApiBlackSort, is_dt_selector)
{
  Cvc5Sort dt_sort = create_datatype_sort();
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sort);
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  ASSERT_DEATH(cvc5_dt_cons_get_selector(cons, 2), "index out of bounds");
  Cvc5DatatypeSelector sel = cvc5_dt_cons_get_selector(cons, 1);
  Cvc5Sort sel_sort = cvc5_term_get_sort(cvc5_dt_sel_get_term(sel));
  ASSERT_FALSE(cvc5_sort_is_dt_selector(nullptr));
  ASSERT_TRUE(cvc5_sort_is_dt_selector(sel_sort));
  ASSERT_FALSE(cvc5_sort_is_dt_selector(d_int));
}

TEST_F(TestCApiBlackSort, is_dt_tester)
{
  Cvc5Sort dt_sort = create_datatype_sort();
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sort);
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  Cvc5Term tester = cvc5_dt_cons_get_tester_term(cons);
  Cvc5Sort tester_sort = cvc5_term_get_sort(tester);
  ASSERT_FALSE(cvc5_sort_is_dt_tester(nullptr));
  ASSERT_TRUE(cvc5_sort_is_dt_tester(tester_sort));
  ASSERT_FALSE(cvc5_sort_is_dt_tester(d_int));
}

TEST_F(TestCApiBlackSort, is_dt_updater)
{
  Cvc5Sort dt_sort = create_datatype_sort();
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sort);
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  Cvc5DatatypeSelector sel = cvc5_dt_cons_get_selector(cons, 1);
  Cvc5Term updater = cvc5_dt_sel_get_updater_term(sel);
  Cvc5Sort updater_sort = cvc5_term_get_sort(updater);
  ASSERT_FALSE(cvc5_sort_is_dt_updater(nullptr));
  ASSERT_TRUE(cvc5_sort_is_dt_updater(updater_sort));
  ASSERT_FALSE(cvc5_sort_is_dt_updater(d_int));
}

TEST_F(TestCApiBlackSort, is_fun)
{
  std::vector<Cvc5Sort> domain = {d_real};
  Cvc5Sort sort = cvc5_mk_fun_sort(d_tm, 1, domain.data(), d_int);
  ASSERT_FALSE(cvc5_sort_is_fun(nullptr));
  ASSERT_TRUE(cvc5_sort_is_fun(sort));
  ASSERT_FALSE(cvc5_sort_is_fun(d_int));
}

TEST_F(TestCApiBlackSort, is_predicate)
{
  std::vector<Cvc5Sort> args = {d_real};
  Cvc5Sort sort = cvc5_mk_predicate_sort(d_tm, 1, args.data());
  ASSERT_FALSE(cvc5_sort_is_predicate(nullptr));
  ASSERT_TRUE(cvc5_sort_is_predicate(sort));
  ASSERT_FALSE(cvc5_sort_is_predicate(d_int));
}

TEST_F(TestCApiBlackSort, is_tuple)
{
  std::vector<Cvc5Sort> args = {d_real};
  Cvc5Sort sort = cvc5_mk_tuple_sort(d_tm, 1, args.data());
  ASSERT_FALSE(cvc5_sort_is_tuple(nullptr));
  ASSERT_TRUE(cvc5_sort_is_tuple(sort));
  ASSERT_FALSE(cvc5_sort_is_tuple(d_int));
}

TEST_F(TestCApiBlackSort, is_nullable)
{
  Cvc5Sort sort = cvc5_mk_nullable_sort(d_tm, d_real);
  ASSERT_FALSE(cvc5_sort_is_nullable(nullptr));
  ASSERT_TRUE(cvc5_sort_is_nullable(sort));
  ASSERT_FALSE(cvc5_sort_is_nullable(d_int));
}

TEST_F(TestCApiBlackSort, is_record)
{
  std::vector<const char*> names = {"asdf"};
  std::vector<Cvc5Sort> args = {d_real};
  Cvc5Sort sort = cvc5_mk_record_sort(d_tm, 1, names.data(), args.data());
  ASSERT_FALSE(cvc5_sort_is_record(nullptr));
  ASSERT_TRUE(cvc5_sort_is_record(sort));
  ASSERT_FALSE(cvc5_sort_is_record(d_int));
}

TEST_F(TestCApiBlackSort, is_array)
{
  Cvc5Sort sort = cvc5_mk_array_sort(d_tm, d_real, d_int);
  ASSERT_FALSE(cvc5_sort_is_array(nullptr));
  ASSERT_TRUE(cvc5_sort_is_array(sort));
  ASSERT_FALSE(cvc5_sort_is_array(d_int));
}

TEST_F(TestCApiBlackSort, is_set)
{
  Cvc5Sort sort = cvc5_mk_set_sort(d_tm, d_int);
  ASSERT_FALSE(cvc5_sort_is_set(nullptr));
  ASSERT_TRUE(cvc5_sort_is_set(sort));
  ASSERT_FALSE(cvc5_sort_is_set(d_int));
}

TEST_F(TestCApiBlackSort, is_bag)
{
  Cvc5Sort sort = cvc5_mk_bag_sort(d_tm, d_int);
  ASSERT_FALSE(cvc5_sort_is_bag(nullptr));
  ASSERT_TRUE(cvc5_sort_is_bag(sort));
  ASSERT_FALSE(cvc5_sort_is_bag(d_int));
}

TEST_F(TestCApiBlackSort, is_sequence)
{
  Cvc5Sort sort = cvc5_mk_sequence_sort(d_tm, d_int);
  ASSERT_FALSE(cvc5_sort_is_sequence(nullptr));
  ASSERT_TRUE(cvc5_sort_is_sequence(sort));
  ASSERT_FALSE(cvc5_sort_is_sequence(d_int));
}

TEST_F(TestCApiBlackSort, is_abstract)
{
  ASSERT_FALSE(cvc5_sort_is_abstract(nullptr));
  ASSERT_TRUE(cvc5_sort_is_abstract(
      cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_BITVECTOR_SORT)));
  // ?Array is syntax sugar for (Array ? ?), thus the constructed sort
  // is an Array sort, not an abstract sort.
  ASSERT_FALSE(cvc5_sort_is_abstract(
      cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_ARRAY_SORT)));
  ASSERT_TRUE(cvc5_sort_is_abstract(
      cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_ABSTRACT_SORT)));
  ASSERT_FALSE(cvc5_sort_is_abstract(d_int));
}

TEST_F(TestCApiBlackSort, is_uninterpreted)
{
  ASSERT_FALSE(cvc5_sort_is_uninterpreted_sort(nullptr));
  ASSERT_TRUE(cvc5_sort_is_uninterpreted_sort(
      cvc5_mk_uninterpreted_sort(d_tm, "asdf")));
  ASSERT_TRUE(cvc5_sort_is_uninterpreted_sort(
      cvc5_mk_uninterpreted_sort(d_tm, nullptr)));
}

TEST_F(TestCApiBlackSort, is_uninterpreted_sort_constructor)
{
  ASSERT_FALSE(cvc5_sort_is_uninterpreted_sort_constructor(nullptr));
  ASSERT_TRUE(cvc5_sort_is_uninterpreted_sort_constructor(
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 1, "asdf")));
  ASSERT_TRUE(cvc5_sort_is_uninterpreted_sort_constructor(
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, nullptr)));
}

TEST_F(TestCApiBlackSort, get_datatype)
{
  Cvc5Sort dt_sort = create_datatype_sort();
  (void)cvc5_sort_get_datatype(dt_sort);
  // create bv sort, check should fail
  ASSERT_DEATH(cvc5_sort_get_datatype(d_int), "expected datatype sort");
}

TEST_F(TestCApiBlackSort, dt_domain_codomain_sorts)
{
  size_t size;
  Cvc5Sort sort = create_datatype_sort();
  Cvc5Datatype dt = cvc5_sort_get_datatype(sort);
  ASSERT_FALSE(cvc5_sort_is_dt_constructor(sort));
  ASSERT_DEATH(cvc5_sort_dt_constructor_get_codomain(sort),
               "not a constructor sort");
  ASSERT_DEATH(cvc5_sort_dt_constructor_get_domain(sort, &size),
               "not a constructor sort");
  ASSERT_DEATH(cvc5_sort_dt_constructor_get_arity(sort),
               "not a constructor sort");

  // get constructor
  ASSERT_DEATH(cvc5_dt_get_constructor(nullptr, 0), "invalid datatype");
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  Cvc5Sort cons_sort = cvc5_term_get_sort(cvc5_dt_cons_get_term(cons));
  ASSERT_TRUE(cvc5_sort_is_dt_constructor(cons_sort));
  ASSERT_FALSE(cvc5_sort_is_dt_tester(cons_sort));
  ASSERT_FALSE(cvc5_sort_is_dt_selector(cons_sort));
  ASSERT_EQ(cvc5_sort_dt_constructor_get_arity(cons_sort), 2);
  const Cvc5Sort* domain =
      cvc5_sort_dt_constructor_get_domain(cons_sort, &size);
  ASSERT_TRUE(cvc5_sort_is_equal(domain[0], d_int));
  ASSERT_TRUE(cvc5_sort_is_equal(domain[1], sort));
  ASSERT_TRUE(cvc5_sort_is_equal(
      cvc5_sort_dt_constructor_get_codomain(cons_sort), sort));

  // get tester
  ASSERT_DEATH(cvc5_dt_cons_get_tester_term(nullptr),
               "invalid datatype constructor");
  ASSERT_DEATH(cvc5_sort_dt_tester_get_domain(d_bool), "not a tester sort");
  ASSERT_DEATH(cvc5_sort_dt_tester_get_codomain(d_bool), "not a tester sort");
  Cvc5Term tester = cvc5_dt_cons_get_tester_term(cons);
  Cvc5Sort tester_sort = cvc5_term_get_sort(tester);
  ASSERT_TRUE(cvc5_sort_is_dt_tester(tester_sort));
  ASSERT_TRUE(
      cvc5_sort_is_equal(cvc5_sort_dt_tester_get_domain(tester_sort), sort));
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_sort_dt_tester_get_codomain(tester_sort),
                                 d_bool));

  // get selector
  ASSERT_DEATH(cvc5_dt_cons_get_selector(nullptr, 1),
               "invalid datatype constructor");
  ASSERT_DEATH(cvc5_sort_dt_selector_get_domain(d_bool), "not a selector sort");
  ASSERT_DEATH(cvc5_sort_dt_selector_get_codomain(d_bool),
               "not a selector sort");
  Cvc5DatatypeSelector sel = cvc5_dt_cons_get_selector(cons, 1);
  Cvc5Term tail = cvc5_dt_sel_get_term(sel);
  Cvc5Sort tail_sort = cvc5_term_get_sort(tail);
  ASSERT_TRUE(cvc5_sort_is_dt_selector(tail_sort));
  ASSERT_EQ(cvc5_sort_dt_selector_get_domain(tail_sort), sort);
  ASSERT_EQ(cvc5_sort_dt_selector_get_codomain(tail_sort), sort);
}

TEST_F(TestCApiBlackSort, instantiate)
{
  // instantiate parametric datatype, check should not fail
  Cvc5Sort param_sort = create_param_datatype_sort();
  std::vector<Cvc5Sort> args = {d_int};
  (void)cvc5_sort_instantiate(param_sort, 1, args.data());
  // instantiate non-parametric datatype sort, check should fail
  Cvc5Sort sort = create_datatype_sort();
  ASSERT_DEATH(cvc5_sort_instantiate(sort, 1, args.data()),
               "expected parametric datatype or sort constructor sort");
  // instantiate uninterpreted sort constructor
  Cvc5Sort sort_cons_sort =
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 1, "s");
  (void)cvc5_sort_instantiate(sort_cons_sort, 1, args.data());
}

TEST_F(TestCApiBlackSort, is_instantiated)
{
  std::vector<Cvc5Sort> args = {d_int};
  Cvc5Sort param_sort = create_param_datatype_sort();
  ASSERT_FALSE(cvc5_sort_is_instantiated(param_sort));
  ASSERT_TRUE(cvc5_sort_is_instantiated(
      cvc5_sort_instantiate(param_sort, 1, args.data())));

  Cvc5Sort sort_cons_sort =
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 1, "s");
  ASSERT_FALSE(cvc5_sort_is_instantiated(sort_cons_sort));
  ASSERT_TRUE(cvc5_sort_is_instantiated(
      cvc5_sort_instantiate(sort_cons_sort, 1, args.data())));

  ASSERT_FALSE(cvc5_sort_is_instantiated(d_int));
}

TEST_F(TestCApiBlackSort, get_instantiated_parameters)
{
  size_t size;
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 8);

  // parametric datatype instantiation
  Cvc5Sort p1 = cvc5_mk_param_sort(d_tm, "p1");
  Cvc5Sort p2 = cvc5_mk_param_sort(d_tm, "p2");
  std::vector<Cvc5Sort> sorts = {p1, p2};
  Cvc5DatatypeDecl decl =
      cvc5_mk_dt_decl_with_params(d_tm, "pdtype", 2, sorts.data(), false);
  Cvc5DatatypeConstructorDecl cons1 = cvc5_mk_dt_cons_decl(d_tm, "cons1");
  Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(d_tm, "cons2");
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_cons_decl_add_selector(cons1, "sel", p1);
  cvc5_dt_cons_decl_add_selector(cons2, "sel", p2);
  cvc5_dt_decl_add_constructor(decl, cons1);
  cvc5_dt_decl_add_constructor(decl, cons2);
  cvc5_dt_decl_add_constructor(decl, nil);
  Cvc5Sort sort = cvc5_mk_dt_sort(d_tm, decl);

  ASSERT_DEATH(cvc5_sort_get_instantiated_parameters(nullptr, &size),
               "invalid sort");
  ASSERT_DEATH(cvc5_sort_get_instantiated_parameters(sort, &size),
               "expected instantiated parametric sort");

  {
    std::vector<Cvc5Sort> args = {d_real, d_bool};
    Cvc5Sort inst_sort = cvc5_sort_instantiate(sort, 2, args.data());
    ASSERT_DEATH(cvc5_sort_get_instantiated_parameters(inst_sort, nullptr),
                 "unexpected NULL argument");

    const Cvc5Sort* inst_sorts =
        cvc5_sort_get_instantiated_parameters(inst_sort, &size);
    ASSERT_TRUE(cvc5_sort_is_equal(inst_sorts[0], d_real));
    ASSERT_TRUE(cvc5_sort_is_equal(inst_sorts[1], d_bool));
  }

  // uninterpreted sort constructor sort instantiation
  Cvc5Sort sort_cons_sort =
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 4, "a");
  ASSERT_DEATH(cvc5_sort_get_instantiated_parameters(sort_cons_sort, &size),
               "expected instantiated parametric sort");

  {
    std::vector<Cvc5Sort> args = {d_bool, d_int, bv_sort, d_real};
    Cvc5Sort inst_sort = cvc5_sort_instantiate(sort_cons_sort, 4, args.data());
    const Cvc5Sort* inst_sorts =
        cvc5_sort_get_instantiated_parameters(inst_sort, &size);
    ASSERT_TRUE(cvc5_sort_is_equal(inst_sorts[0], d_bool));
    ASSERT_TRUE(cvc5_sort_is_equal(inst_sorts[1], d_int));
    ASSERT_TRUE(cvc5_sort_is_equal(inst_sorts[2], bv_sort));
    ASSERT_TRUE(cvc5_sort_is_equal(inst_sorts[3], d_real));
  }

  ASSERT_DEATH(cvc5_sort_get_instantiated_parameters(d_int, &size),
               "expected instantiated parametric sort");
}

TEST_F(TestCApiBlackSort, get_uninterpreted_sort_constructor)
{
  Cvc5Sort bv_sort = cvc5_mk_bv_sort(d_tm, 8);
  Cvc5Sort sort = cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 4, "s");
  std::vector<Cvc5Sort> args = {d_bool, d_int, bv_sort, d_real};
  ASSERT_DEATH(cvc5_sort_get_uninterpreted_sort_constructor(nullptr),
               "invalid sort");
  ASSERT_DEATH(cvc5_sort_get_uninterpreted_sort_constructor(sort),
               "expected instantiated uninterpreted sort");
  Cvc5Sort inst_sort = cvc5_sort_instantiate(sort, 4, args.data());
  ASSERT_TRUE(cvc5_sort_is_equal(
      sort, cvc5_sort_get_uninterpreted_sort_constructor(inst_sort)));
}

TEST_F(TestCApiBlackSort, get_fun_arity)
{
  std::vector<Cvc5Sort> domain = {cvc5_mk_uninterpreted_sort(d_tm, "u"), d_int};
  Cvc5Sort sort = cvc5_mk_fun_sort(d_tm, 2, domain.data(), d_int);
  ASSERT_EQ(cvc5_sort_fun_get_arity(sort), 2);
  ASSERT_DEATH(cvc5_sort_fun_get_arity(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_fun_get_arity(d_int), "not a function sort");
}

TEST_F(TestCApiBlackSort, get_fun_domain_sorts)
{
  Cvc5Sort usort = cvc5_mk_uninterpreted_sort(d_tm, "u");
  std::vector<Cvc5Sort> domain = {usort, d_int};
  Cvc5Sort sort = cvc5_mk_fun_sort(d_tm, 2, domain.data(), d_int);
  size_t size;
  const Cvc5Sort* sorts = cvc5_sort_fun_get_domain(sort, &size);
  ASSERT_EQ(size, 2);
  ASSERT_TRUE(cvc5_sort_is_equal(sorts[0], usort));
  ASSERT_TRUE(cvc5_sort_is_equal(sorts[1], d_int));
  ASSERT_DEATH(cvc5_sort_fun_get_domain(nullptr, &size), "invalid sort");
  ASSERT_DEATH(cvc5_sort_fun_get_domain(sort, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_sort_fun_get_domain(d_int, &size), "not a function sort");
}

TEST_F(TestCApiBlackSort, get_fun_codomain)
{
  Cvc5Sort usort = cvc5_mk_uninterpreted_sort(d_tm, "u");
  std::vector<Cvc5Sort> domain = {usort, d_int};
  Cvc5Sort sort = cvc5_mk_fun_sort(d_tm, 2, domain.data(), d_int);
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_sort_fun_get_codomain(sort), d_int));
  ASSERT_DEATH(cvc5_sort_fun_get_codomain(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_fun_get_codomain(d_int), "not a function sort");
}

TEST_F(TestCApiBlackSort, get_array_index_element)
{
  Cvc5Sort elem_sort = cvc5_mk_bv_sort(d_tm, 32);
  Cvc5Sort index_sort = cvc5_mk_bv_sort(d_tm, 32);
  Cvc5Sort sort = cvc5_mk_array_sort(d_tm, index_sort, elem_sort);
  ASSERT_TRUE(
      cvc5_sort_is_equal(cvc5_sort_array_get_index_sort(sort), index_sort));
  ASSERT_TRUE(
      cvc5_sort_is_equal(cvc5_sort_array_get_element_sort(sort), elem_sort));
  ASSERT_DEATH(cvc5_sort_array_get_index_sort(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_array_get_element_sort(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_array_get_index_sort(d_int), "not an array sort");
  ASSERT_DEATH(cvc5_sort_array_get_element_sort(d_int), "not an array sort");
}

TEST_F(TestCApiBlackSort, get_set_element)
{
  Cvc5Sort sort = cvc5_mk_set_sort(d_tm, d_int);
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_sort_set_get_element_sort(sort), d_int));
  ASSERT_DEATH(cvc5_sort_set_get_element_sort(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_set_get_element_sort(d_int), "not a set sort");
}

TEST_F(TestCApiBlackSort, get_bag_element)
{
  Cvc5Sort sort = cvc5_mk_bag_sort(d_tm, d_int);
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_sort_bag_get_element_sort(sort), d_int));
  ASSERT_DEATH(cvc5_sort_bag_get_element_sort(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_bag_get_element_sort(d_int), "not a bag sort");
}

TEST_F(TestCApiBlackSort, get_sequence_element)
{
  Cvc5Sort sort = cvc5_mk_sequence_sort(d_tm, d_int);
  ASSERT_TRUE(
      cvc5_sort_is_equal(cvc5_sort_sequence_get_element_sort(sort), d_int));
  ASSERT_DEATH(cvc5_sort_sequence_get_element_sort(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_sequence_get_element_sort(d_int),
               "not a sequence sort");
}

TEST_F(TestCApiBlackSort, abstract_get_kind)
{
  Cvc5Sort sort = cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_BITVECTOR_SORT);
  ASSERT_EQ(cvc5_sort_abstract_get_kind(sort), CVC5_SORT_KIND_BITVECTOR_SORT);
  // ?Array is syntax sugar for (Array ? ?), thus the constructed sort
  // is an Array sort, not an abstract sort and its abstract kind cannot be
  // extracted.
  sort = cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_ARRAY_SORT);
  ASSERT_DEATH(cvc5_sort_abstract_get_kind(sort), "not an abstract sort");
  sort = cvc5_mk_abstract_sort(d_tm, CVC5_SORT_KIND_ABSTRACT_SORT);
  ASSERT_EQ(cvc5_sort_abstract_get_kind(sort), CVC5_SORT_KIND_ABSTRACT_SORT);
}

TEST_F(TestCApiBlackSort, get_uninterpreted_sort_constructor_name)
{
  Cvc5Sort sort = cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, "s");
  ASSERT_EQ(cvc5_sort_get_symbol(sort), std::string("s"));
  ASSERT_DEATH(cvc5_sort_get_symbol(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_get_symbol(d_int), "has no symbol");
}

TEST_F(TestCApiBlackSort, uninterpreted_sort_constructor_get_arity)
{
  Cvc5Sort sort = cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 2, "s");
  ASSERT_EQ(cvc5_sort_uninterpreted_sort_constructor_get_arity(sort), 2);
  ASSERT_DEATH(cvc5_sort_uninterpreted_sort_constructor_get_arity(nullptr),
               "invalid sort");
  ASSERT_DEATH(cvc5_sort_uninterpreted_sort_constructor_get_arity(d_int),
               "not a sort constructor sort");
}

TEST_F(TestCApiBlackSort, bv_get_size)
{
  Cvc5Sort sort = cvc5_mk_bv_sort(d_tm, 32);
  ASSERT_EQ(cvc5_sort_bv_get_size(sort), 32);
  ASSERT_DEATH(cvc5_sort_bv_get_size(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_bv_get_size(d_int), "not a bit-vector sort");
}

TEST_F(TestCApiBlackSort, ff_get_size)
{
  Cvc5Sort sort = cvc5_mk_ff_sort(d_tm, "31", 10);
  ASSERT_EQ(cvc5_sort_ff_get_size(sort), std::string("31"));
  ASSERT_DEATH(cvc5_sort_ff_get_size(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_ff_get_size(d_int), "not a finite field sort");
}

TEST_F(TestCApiBlackSort, fp_get_exp_sig_size)
{
  Cvc5Sort sort = cvc5_mk_fp_sort(d_tm, 8, 24);
  ASSERT_EQ(cvc5_sort_fp_get_exp_size(sort), 8);
  ASSERT_EQ(cvc5_sort_fp_get_sig_size(sort), 24);
  ASSERT_DEATH(cvc5_sort_fp_get_exp_size(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_fp_get_exp_size(d_int), "not a floating-point sort");
  ASSERT_DEATH(cvc5_sort_fp_get_sig_size(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_fp_get_sig_size(d_int), "not a floating-point sort");
}

TEST_F(TestCApiBlackSort, dt_get_arity)
{
  // create datatype sort, check should not fail
  Cvc5Sort sort = create_datatype_sort();
  ASSERT_EQ(cvc5_sort_dt_get_arity(sort), 0);
  // create bv sort, check should fail
  ASSERT_DEATH(cvc5_sort_dt_get_arity(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_dt_get_arity(d_int), "not a datatype sort");
}

TEST_F(TestCApiBlackSort, tuple_get_length)
{
  std::vector<Cvc5Sort> args = {d_int, d_int};
  Cvc5Sort sort = cvc5_mk_tuple_sort(d_tm, 2, args.data());
  ASSERT_EQ(cvc5_sort_tuple_get_length(sort), 2);
  ASSERT_DEATH(cvc5_sort_tuple_get_length(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_tuple_get_length(d_int), "not a tuple sort");
}

TEST_F(TestCApiBlackSort, tuple_get_element_sorts)
{
  size_t size;
  std::vector<Cvc5Sort> args = {d_int, d_int};
  Cvc5Sort sort = cvc5_mk_tuple_sort(d_tm, 2, args.data());
  const Cvc5Sort* sorts = cvc5_sort_tuple_get_element_sorts(sort, &size);
  ASSERT_TRUE(cvc5_sort_is_equal(sorts[0], d_int));
  ASSERT_TRUE(cvc5_sort_is_equal(sorts[1], d_int));
  ASSERT_DEATH(cvc5_sort_tuple_get_element_sorts(nullptr, &size),
               "invalid sort");
  ASSERT_DEATH(cvc5_sort_tuple_get_element_sorts(sort, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_sort_tuple_get_element_sorts(d_int, &size),
               "not a tuple sort");
}

TEST_F(TestCApiBlackSort, nullable_get_element_sort)
{
  Cvc5Sort sort = cvc5_mk_nullable_sort(d_tm, d_real);
  ASSERT_TRUE(
      cvc5_sort_is_equal(cvc5_sort_nullable_get_element_sort(sort), d_real));
  ASSERT_DEATH(cvc5_sort_nullable_get_element_sort(nullptr), "invalid sort");
  ASSERT_DEATH(cvc5_sort_nullable_get_element_sort(d_int),
               "not a nullable sort");
}

TEST_F(TestCApiBlackSort, scoped_to_string)
{
  std::string name = "uninterp-sort";
  Cvc5Sort bvsort = cvc5_mk_bv_sort(d_tm, 8);
  Cvc5Sort usort = cvc5_mk_uninterpreted_sort(d_tm, name.c_str());
  ASSERT_EQ(cvc5_sort_to_string(bvsort), std::string("(_ BitVec 8)"));
  ASSERT_EQ(cvc5_sort_to_string(usort), name);
  ASSERT_EQ(cvc5_sort_to_string(bvsort), std::string("(_ BitVec 8)"));
  ASSERT_EQ(cvc5_sort_to_string(usort), name);
}

TEST_F(TestCApiBlackSort, substitute)
{
  Cvc5Sort p0 = cvc5_mk_param_sort(d_tm, "T0");
  Cvc5Sort p1 = cvc5_mk_param_sort(d_tm, "T1");
  Cvc5Sort arrsort0 = cvc5_mk_array_sort(d_tm, p0, p0);
  Cvc5Sort arrsort1 = cvc5_mk_array_sort(d_tm, p1, p1);
  // Now create instantiations of the defined sorts
  (void)cvc5_sort_substitute(arrsort0, p0, d_int);
  std::vector<Cvc5Sort> sorts = {p0, p1};
  std::vector<Cvc5Sort> replacements = {d_int, d_real};
  (void)cvc5_sort_substitute_sorts(
      arrsort1, 2, sorts.data(), replacements.data());
}

}  // namespace cvc5::internal::test
