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
 * Black box testing of the datatype classes of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackDatatype : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_int = cvc5_get_integer_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
    d_uninterpreted = cvc5_mk_uninterpreted_sort(d_tm, "u");
  }

  void TearDown() override { cvc5_term_manager_delete(d_tm); }

  Cvc5DatatypeDecl create_datatype_decl()
  {
    Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
    Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
    cvc5_dt_cons_decl_add_selector(cons, "head", cvc5_get_integer_sort(d_tm));
    cvc5_dt_cons_decl_add_selector_self(cons, "tail");
    cvc5_dt_decl_add_constructor(decl, cons);
    Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
    cvc5_dt_decl_add_constructor(decl, nil);
    return decl;
  }

  Cvc5Datatype create_datatype()
  {
    Cvc5DatatypeDecl decl = create_datatype_decl();
    return cvc5_sort_get_datatype(cvc5_mk_dt_sort(d_tm, decl));
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
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackDatatype, mk_dt_sort)
{
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", d_int);
  cvc5_dt_decl_add_constructor(decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);

  ASSERT_DEATH(cvc5_mk_dt_sort(nullptr, decl), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_dt_sort(d_tm, nullptr), "invalid datatype declaration");
  Cvc5Sort list_sort = cvc5_mk_dt_sort(d_tm, decl);
  Cvc5Datatype dt = cvc5_sort_get_datatype(list_sort);
  Cvc5DatatypeConstructor cons_cons = cvc5_dt_get_constructor(dt, 0);
  Cvc5DatatypeConstructor cons_nil = cvc5_dt_get_constructor(dt, 1);
  ASSERT_DEATH(cvc5_dt_get_constructor(dt, 2), "index out of bounds");
  (void)cvc5_dt_cons_get_term(cons_cons);
  (void)cvc5_dt_cons_get_term(cons_nil);
}

TEST_F(TestCApiBlackDatatype, equal_hash)
{
  Cvc5DatatypeDecl decl1 = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons1 = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons1, "head", d_int);
  cvc5_dt_decl_add_constructor(decl1, cons1);
  Cvc5DatatypeConstructorDecl nil1 = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl1, nil1);
  Cvc5Sort list1 = cvc5_mk_dt_sort(d_tm, decl1);
  Cvc5Datatype dt1 = cvc5_sort_get_datatype(list1);
  Cvc5DatatypeConstructor cons_cons1 = cvc5_dt_get_constructor(dt1, 0);
  Cvc5DatatypeConstructor cons_nil1 = cvc5_dt_get_constructor(dt1, 1);
  Cvc5DatatypeSelector head1 =
      cvc5_dt_cons_get_selector_by_name(cons_cons1, "head");

  Cvc5DatatypeDecl decl2 = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons2 = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons2, "head", d_int);
  cvc5_dt_decl_add_constructor(decl2, cons2);
  Cvc5DatatypeConstructorDecl nil2 = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl2, nil2);
  Cvc5Sort list2 = cvc5_mk_dt_sort(d_tm, decl2);
  Cvc5Datatype dt2 = cvc5_sort_get_datatype(list2);
  Cvc5DatatypeConstructor cons_cons2 = cvc5_dt_get_constructor(dt2, 0);
  Cvc5DatatypeConstructor cons_nil2 = cvc5_dt_get_constructor(dt2, 1);
  Cvc5DatatypeSelector head2 =
      cvc5_dt_cons_get_selector_by_name(cons_cons2, "head");

  ASSERT_FALSE(cvc5_dt_decl_is_equal(nullptr, decl1));
  ASSERT_FALSE(cvc5_dt_decl_is_equal(decl1, nullptr));
  ASSERT_FALSE(cvc5_dt_cons_decl_is_equal(nullptr, cons1));
  ASSERT_FALSE(cvc5_dt_cons_decl_is_equal(cons1, nullptr));
  ASSERT_FALSE(cvc5_dt_cons_is_equal(nullptr, cons_cons1));
  ASSERT_FALSE(cvc5_dt_cons_is_equal(cons_cons1, nullptr));
  ASSERT_FALSE(cvc5_dt_sel_is_equal(nullptr, head1));
  ASSERT_FALSE(cvc5_dt_sel_is_equal(head1, nullptr));
  ASSERT_FALSE(cvc5_dt_is_equal(nullptr, dt1));
  ASSERT_FALSE(cvc5_dt_is_equal(dt1, nullptr));

  ASSERT_TRUE(cvc5_dt_decl_is_equal(decl1, decl1));
  ASSERT_FALSE(cvc5_dt_decl_is_equal(decl1, decl2));
  ASSERT_TRUE(cvc5_dt_cons_decl_is_equal(cons1, cons1));
  ASSERT_FALSE(cvc5_dt_cons_decl_is_equal(cons1, cons2));
  ASSERT_TRUE(cvc5_dt_cons_decl_is_equal(nil1, nil1));
  ASSERT_FALSE(cvc5_dt_cons_decl_is_equal(nil1, nil2));
  ASSERT_TRUE(cvc5_dt_cons_is_equal(cons_cons1, cons_cons1));
  ASSERT_FALSE(cvc5_dt_cons_is_equal(cons_cons1, cons_cons2));
  ASSERT_TRUE(cvc5_dt_cons_is_equal(cons_nil1, cons_nil1));
  ASSERT_FALSE(cvc5_dt_cons_is_equal(cons_nil1, cons_nil2));
  ASSERT_TRUE(cvc5_dt_sel_is_equal(head1, head1));
  ASSERT_FALSE(cvc5_dt_sel_is_equal(head1, head2));
  ASSERT_TRUE(cvc5_dt_is_equal(dt1, dt1));
  ASSERT_FALSE(cvc5_dt_is_equal(dt1, dt2));

  ASSERT_DEATH(cvc5_dt_cons_decl_hash(nullptr),
               "invalid datatype constructor declaration");
  ASSERT_DEATH(cvc5_dt_decl_hash(nullptr), "invalid datatype declaration");
  ASSERT_DEATH(cvc5_dt_cons_hash(nullptr), "invalid datatype constructor");
  ASSERT_DEATH(cvc5_dt_sel_hash(nullptr), "invalid datatype selector");
  ASSERT_DEATH(cvc5_dt_hash(nullptr), "invalid datatype");

  ASSERT_EQ(cvc5_dt_decl_hash(decl1), cvc5_dt_decl_hash(decl1));
  ASSERT_EQ(cvc5_dt_decl_hash(decl1), cvc5_dt_decl_hash(decl2));
  ASSERT_EQ(cvc5_dt_cons_decl_hash(cons1), cvc5_dt_cons_decl_hash(cons1));
  ASSERT_EQ(cvc5_dt_cons_decl_hash(cons1), cvc5_dt_cons_decl_hash(cons2));
  ASSERT_EQ(cvc5_dt_cons_decl_hash(nil1), cvc5_dt_cons_decl_hash(nil1));
  ASSERT_EQ(cvc5_dt_cons_decl_hash(nil1), cvc5_dt_cons_decl_hash(nil2));
  ASSERT_EQ(cvc5_dt_cons_hash(cons_cons1), cvc5_dt_cons_hash(cons_cons1));
  ASSERT_EQ(cvc5_dt_cons_hash(cons_cons1), cvc5_dt_cons_hash(cons_cons2));
  ASSERT_EQ(cvc5_dt_sel_hash(head1), cvc5_dt_sel_hash(head1));
  ASSERT_EQ(cvc5_dt_sel_hash(head1), cvc5_dt_sel_hash(head2));
  ASSERT_EQ(cvc5_dt_hash(dt1), cvc5_dt_hash(dt1));
  ASSERT_EQ(cvc5_dt_hash(dt1), cvc5_dt_hash(dt2));
}

TEST_F(TestCApiBlackDatatype, mk_datatype_sorts)
{
  /* Create two mutual datatypes corresponding to this definition
   * block:
   *
   *   DATATYPE
   *     tree = node(left: tree, right: tree) | leaf(data: list),
   *     list = cons(car: tree, cdr: list) | nil
   *   END;
   */
  // Make unresolved types as placeholders
  Cvc5Sort unres_tree = cvc5_mk_unresolved_dt_sort(d_tm, "tree", 0);
  Cvc5Sort unres_list = cvc5_mk_unresolved_dt_sort(d_tm, "list", 0);

  Cvc5DatatypeDecl tree = cvc5_mk_dt_decl(d_tm, "tree", false);
  Cvc5DatatypeConstructorDecl node = cvc5_mk_dt_cons_decl(d_tm, "node");
  cvc5_dt_cons_decl_add_selector(node, "left", unres_tree);
  cvc5_dt_cons_decl_add_selector(node, "right", unres_tree);
  cvc5_dt_decl_add_constructor(tree, node);

  Cvc5DatatypeConstructorDecl leaf = cvc5_mk_dt_cons_decl(d_tm, "leaf");
  cvc5_dt_cons_decl_add_selector(leaf, "data", unres_list);
  cvc5_dt_decl_add_constructor(tree, leaf);

  Cvc5DatatypeDecl list = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "car", unres_tree);
  cvc5_dt_cons_decl_add_selector(cons, "cdr", unres_tree);
  cvc5_dt_decl_add_constructor(list, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(list, nil);

  std::vector<Cvc5DatatypeDecl> dtdecls{tree, list};
  const Cvc5Sort* dtsorts =
      cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  for (size_t i = 0, size = dtdecls.size(); i < size; i++)
  {
    ASSERT_TRUE(cvc5_sort_is_dt(dtsorts[i]));
    ASSERT_FALSE(cvc5_dt_is_finite(cvc5_sort_get_datatype(dtsorts[i])));
    ASSERT_EQ(std::string(cvc5_dt_get_name(cvc5_sort_get_datatype(dtsorts[i]))),
              cvc5_dt_decl_get_name(dtdecls[i]));
  }

  // verify the resolution was correct
  Cvc5Datatype dt_tree = cvc5_sort_get_datatype(dtsorts[0]);
  Cvc5DatatypeConstructor dt_tree_node = cvc5_dt_get_constructor(dt_tree, 0);
  ASSERT_EQ(cvc5_dt_cons_get_name(dt_tree_node), std::string("node"));
  Cvc5DatatypeSelector dt_tree_node_left =
      cvc5_dt_cons_get_selector(dt_tree_node, 0);
  ASSERT_EQ(cvc5_dt_sel_get_name(dt_tree_node_left), std::string("left"));
  // argument type should have resolved to be recursive
  ASSERT_TRUE(
      cvc5_sort_is_dt(cvc5_dt_sel_get_codomain_sort(dt_tree_node_left)));
  ASSERT_TRUE(cvc5_sort_is_equal(
      cvc5_dt_sel_get_codomain_sort(dt_tree_node_left), dtsorts[0]));

  ASSERT_DEATH(cvc5_mk_dt_sorts(nullptr, dtdecls.size(), dtdecls.data()),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_dt_sorts(d_tm, dtdecls.size(), nullptr),
               "unexpected NULL argument");

  // fails due to empty datatype
  std::vector<Cvc5DatatypeDecl> dtdecls_bad{
      cvc5_mk_dt_decl(d_tm, "emptyD", false)};
  ASSERT_DEATH(cvc5_mk_dt_sorts(d_tm, dtdecls_bad.size(), dtdecls_bad.data()),
               "invalid datatype declaration");
}

TEST_F(TestCApiBlackDatatype, dt_cons_decl_copy_release)
{
  ASSERT_DEATH(cvc5_dt_cons_decl_copy(nullptr),
               "invalid datatype constructor declaration");
  ASSERT_DEATH(cvc5_dt_cons_decl_release(nullptr),
               "invalid datatype constructor declaration");
  Cvc5DatatypeConstructorDecl decl = cvc5_mk_dt_cons_decl(d_tm, "cons");
  Cvc5DatatypeConstructorDecl decl_copy = cvc5_dt_cons_decl_copy(decl);
  ASSERT_EQ(cvc5_dt_cons_decl_hash(decl), cvc5_dt_cons_decl_hash(decl_copy));
  cvc5_dt_cons_decl_release(decl);
  ASSERT_EQ(cvc5_dt_cons_decl_hash(decl), cvc5_dt_cons_decl_hash(decl_copy));
  cvc5_dt_cons_decl_release(decl);
  // we cannot reliably check that querying on the (now freed) datatype
  // constructor declaration fails unless ASAN is enabled
}

TEST_F(TestCApiBlackDatatype, dt_cons_decl_add_selector)
{
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector(nullptr, "foo", d_int),
               "invalid datatype constructor declaration");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector(cons, nullptr, d_int),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector(cons, "foo", nullptr),
               "invalid sort");
}

TEST_F(TestCApiBlackDatatype, dt_cons_decl_add_selector_self)
{
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector_self(nullptr, "foo"),
               "invalid datatype constructor declaration");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector_self(cons, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_cons_decl_add_selector_unresolved)
{
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector_unresolved(nullptr, "foo", "bar"),
               "invalid datatype constructor declaration");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector_unresolved(cons, nullptr, "bar"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector_unresolved(cons, "foo", nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_cons_decl_to_string)
{
  ASSERT_DEATH(cvc5_dt_cons_decl_to_string(nullptr),
               "invalid datatype constructor declaration");
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  (void)cvc5_dt_cons_decl_to_string(cons);
}

TEST_F(TestCApiBlackDatatype, dt_cons_decl_hash)
{
  ASSERT_DEATH(cvc5_dt_cons_decl_hash(nullptr),
               "invalid datatype constructor declaration");
}

TEST_F(TestCApiBlackDatatype, dt_decl_copy_release)
{
  ASSERT_DEATH(cvc5_dt_decl_copy(nullptr), "invalid datatype declaration");
  ASSERT_DEATH(cvc5_dt_decl_release(nullptr), "invalid datatype declaration");
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "tree", false);
  Cvc5DatatypeDecl decl_copy = cvc5_dt_decl_copy(decl);
  ASSERT_EQ(cvc5_dt_decl_hash(decl), cvc5_dt_decl_hash(decl_copy));
  cvc5_dt_decl_release(decl);
  ASSERT_EQ(cvc5_dt_decl_hash(decl), cvc5_dt_decl_hash(decl_copy));
  cvc5_dt_decl_release(decl);
  // we cannot reliably check that querying on the (now freed) datatype
  // declaration fails unless ASAN is enabled
}

TEST_F(TestCApiBlackDatatype, dt_decl_add_constructor)
{
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "tree", false);
  Cvc5DatatypeConstructorDecl node = cvc5_mk_dt_cons_decl(d_tm, "node");
  ASSERT_DEATH(cvc5_dt_decl_add_constructor(nullptr, node),
               "invalid datatype declaration");
  ASSERT_DEATH(cvc5_dt_decl_add_constructor(decl, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_decl_get_num_constructors)
{
  ASSERT_DEATH(cvc5_dt_decl_get_num_constructors(nullptr),
               "invalid datatype declaration");
  Cvc5DatatypeDecl decl = create_datatype_decl();
  ASSERT_EQ(cvc5_dt_decl_get_num_constructors(decl), 2);
}

TEST_F(TestCApiBlackDatatype, dt_decl_is_parametric)
{
  ASSERT_DEATH(cvc5_dt_decl_is_parametric(nullptr),
               "invalid datatype declaration");
  Cvc5DatatypeDecl decl = create_datatype_decl();
  ASSERT_FALSE(cvc5_dt_decl_is_parametric(decl));
}

TEST_F(TestCApiBlackDatatype, dt_decl_is_resolved)
{
  ASSERT_DEATH(cvc5_dt_decl_is_resolved(nullptr),
               "invalid datatype declaration");
  Cvc5DatatypeDecl decl = create_datatype_decl();
  ASSERT_FALSE(cvc5_dt_decl_is_resolved(decl));
}

TEST_F(TestCApiBlackDatatype, dt_decl_get_name)
{
  ASSERT_DEATH(cvc5_dt_decl_get_name(nullptr), "invalid datatype declaration");
  Cvc5DatatypeDecl decl = create_datatype_decl();
  ASSERT_EQ(cvc5_dt_decl_get_name(decl), std::string("list"));
}

TEST_F(TestCApiBlackDatatype, dt_decl_to_string)
{
  ASSERT_DEATH(cvc5_dt_decl_to_string(nullptr), "invalid datatype declaration");
}

TEST_F(TestCApiBlackDatatype, dt_decl_hash)
{
  ASSERT_DEATH(cvc5_dt_decl_hash(nullptr), "invalid datatype declaration");
}

TEST_F(TestCApiBlackDatatype, dt_sel_copy_release)
{
  ASSERT_DEATH(cvc5_dt_sel_copy(nullptr), "invalid datatype selector");
  ASSERT_DEATH(cvc5_dt_sel_release(nullptr), "invalid datatype selector");
  Cvc5Datatype dt = create_datatype();
  Cvc5DatatypeSelector sel = cvc5_dt_get_selector(dt, "head");
  Cvc5DatatypeSelector sel_copy = cvc5_dt_sel_copy(sel);
  ASSERT_EQ(cvc5_dt_sel_hash(sel), cvc5_dt_sel_hash(sel_copy));
  cvc5_dt_sel_release(sel);
  ASSERT_EQ(cvc5_dt_sel_hash(sel), cvc5_dt_sel_hash(sel_copy));
  cvc5_dt_sel_release(sel);
  // we cannot reliably check that querying on the (now freed) datatype
  // selector fails unless ASAN is enabled
}

TEST_F(TestCApiBlackDatatype, dt_sel_get_name)
{
  ASSERT_DEATH(cvc5_dt_sel_get_name(nullptr), "invalid datatype selector");
}

TEST_F(TestCApiBlackDatatype, dt_sel_get_term)
{
  ASSERT_DEATH(cvc5_dt_sel_get_term(nullptr), "invalid datatype selector");
}

TEST_F(TestCApiBlackDatatype, dt_sel_get_updater_term)
{
  ASSERT_DEATH(cvc5_dt_sel_get_updater_term(nullptr),
               "invalid datatype selector");
}

TEST_F(TestCApiBlackDatatype, dt_sel_get_codomain_sort)
{
  ASSERT_DEATH(cvc5_dt_sel_get_codomain_sort(nullptr),
               "invalid datatype selector");
}

TEST_F(TestCApiBlackDatatype, dt_sel_to_string)
{
  ASSERT_DEATH(cvc5_dt_sel_to_string(nullptr), "invalid datatype selector");
  Cvc5Datatype dt = create_datatype();
  Cvc5DatatypeSelector head =
      cvc5_dt_cons_get_selector_by_name(cvc5_dt_get_constructor(dt, 0), "head");
  ASSERT_EQ(cvc5_dt_sel_to_string(head), std::string("head: Int"));
}

TEST_F(TestCApiBlackDatatype, dt_sel_hash)
{
  ASSERT_DEATH(cvc5_dt_sel_hash(nullptr), "invalid datatype selector");
}

TEST_F(TestCApiBlackDatatype, dt_cons_copy_release)
{
  ASSERT_DEATH(cvc5_dt_cons_copy(nullptr), "invalid datatype constructor");
  ASSERT_DEATH(cvc5_dt_cons_release(nullptr), "invalid datatype constructor");
  Cvc5Datatype dt = create_datatype();
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  Cvc5DatatypeConstructor cons_copy = cvc5_dt_cons_copy(cons);
  ASSERT_EQ(cvc5_dt_cons_hash(cons), cvc5_dt_cons_hash(cons_copy));
  cvc5_dt_cons_release(cons);
  ASSERT_EQ(cvc5_dt_cons_hash(cons), cvc5_dt_cons_hash(cons_copy));
  cvc5_dt_cons_release(cons);
  // we cannot reliably check that querying on the (now freed) datatype
  // constructor fails unless ASAN is enabled
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_name)
{
  ASSERT_DEATH(cvc5_dt_cons_get_name(nullptr), "invalid datatype constructor");
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_term)
{
  ASSERT_DEATH(cvc5_dt_cons_get_term(nullptr), "invalid datatype constructor");
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_instantiated_term)
{
  Cvc5Datatype dt = create_datatype();
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  ASSERT_DEATH(cvc5_dt_cons_get_instantiated_term(nullptr, d_int),
               "invalid datatype constructor");
  ASSERT_DEATH(cvc5_dt_cons_get_instantiated_term(cons, nullptr),
               "invalid sort");
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_tester_term)
{
  ASSERT_DEATH(cvc5_dt_cons_get_tester_term(nullptr),
               "invalid datatype constructor");
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_num_selectors)
{
  ASSERT_DEATH(cvc5_dt_cons_get_num_selectors(nullptr),
               "invalid datatype constructor");
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_selector)
{
  ASSERT_DEATH(cvc5_dt_cons_get_selector(nullptr, 0),
               "invalid datatype constructor");
}

TEST_F(TestCApiBlackDatatype, dt_cons_get_selector_by_name)
{
  Cvc5Datatype dt = create_datatype();
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  ASSERT_DEATH(cvc5_dt_cons_get_selector_by_name(nullptr, "cons"),
               "invalid datatype constructor");
  ASSERT_DEATH(cvc5_dt_cons_get_selector_by_name(cons, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_copy_release)
{
  ASSERT_DEATH(cvc5_dt_copy(nullptr), "invalid datatype");
  ASSERT_DEATH(cvc5_dt_release(nullptr), "invalid datatype");
  Cvc5Datatype dt = create_datatype();
  Cvc5Datatype dt_copy = cvc5_dt_copy(dt);
  ASSERT_EQ(cvc5_dt_hash(dt), cvc5_dt_hash(dt_copy));
  cvc5_dt_release(dt);
  ASSERT_EQ(cvc5_dt_hash(dt), cvc5_dt_hash(dt_copy));
  cvc5_dt_release(dt);
  // we cannot reliably check that querying on the (now freed) datatype
  // fails unless ASAN is enabled
}

TEST_F(TestCApiBlackDatatype, dt_cons_to_string)
{
  ASSERT_DEATH(cvc5_dt_cons_to_string(nullptr), "invalid datatype constructor");
  Cvc5Datatype dt = create_datatype();
  Cvc5DatatypeConstructor cons = cvc5_dt_get_constructor(dt, 0);
  ASSERT_EQ(cvc5_dt_cons_to_string(cons),
            std::string("cons(head: Int, tail: list)"));
}

TEST_F(TestCApiBlackDatatype, dt_cons_hash)
{
  ASSERT_DEATH(cvc5_dt_cons_hash(nullptr), "invalid datatype constructor");
}

TEST_F(TestCApiBlackDatatype, dt_get_constructor)
{
  ASSERT_DEATH(cvc5_dt_get_constructor(nullptr, 0), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_get_constructor_by_name)
{
  Cvc5Datatype dt = create_datatype();
  ASSERT_DEATH(cvc5_dt_get_constructor_by_name(nullptr, "cons"),
               "invalid datatype");
  ASSERT_DEATH(cvc5_dt_get_constructor_by_name(dt, nullptr),
               "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_get_selector)
{
  Cvc5Datatype dt = create_datatype();
  ASSERT_DEATH(cvc5_dt_get_selector(nullptr, "cons"), "invalid datatype");
  ASSERT_DEATH(cvc5_dt_get_selector(dt, nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_get_name)
{
  ASSERT_DEATH(cvc5_dt_get_name(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_get_num_constructors)
{
  ASSERT_DEATH(cvc5_dt_get_num_constructors(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_get_parameters)
{
  size_t size;
  Cvc5Datatype dt = create_datatype();
  ASSERT_DEATH(cvc5_dt_get_parameters(nullptr, &size), "invalid datatype");
  ASSERT_DEATH(cvc5_dt_get_parameters(dt, nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackDatatype, dt_is_parametric)
{
  ASSERT_DEATH(cvc5_dt_is_parametric(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_is_codatatype)
{
  ASSERT_DEATH(cvc5_dt_is_codatatype(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_is_tuple)
{
  ASSERT_DEATH(cvc5_dt_is_tuple(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_is_record)
{
  ASSERT_DEATH(cvc5_dt_is_record(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_is_finite)
{
  ASSERT_DEATH(cvc5_dt_is_finite(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_is_well_founded)
{
  ASSERT_DEATH(cvc5_dt_is_well_founded(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_to_string)
{
  ASSERT_DEATH(cvc5_dt_to_string(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, dt_hash)
{
  ASSERT_DEATH(cvc5_dt_hash(nullptr), "invalid datatype");
}

TEST_F(TestCApiBlackDatatype, mk_dt_sorts_sel_unres)
{
  // Same as above, without unresolved sorts

  Cvc5DatatypeDecl tree = cvc5_mk_dt_decl(d_tm, "tree", false);
  Cvc5DatatypeConstructorDecl node = cvc5_mk_dt_cons_decl(d_tm, "node");
  cvc5_dt_cons_decl_add_selector_unresolved(node, "left", "tree");
  cvc5_dt_cons_decl_add_selector_unresolved(node, "right", "tree");
  cvc5_dt_decl_add_constructor(tree, node);

  Cvc5DatatypeConstructorDecl leaf = cvc5_mk_dt_cons_decl(d_tm, "leaf");
  cvc5_dt_cons_decl_add_selector_unresolved(leaf, "data", "list");
  cvc5_dt_decl_add_constructor(tree, leaf);

  Cvc5DatatypeDecl list = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector_unresolved(cons, "car", "tree");
  cvc5_dt_cons_decl_add_selector_unresolved(cons, "cdr", "tree");
  cvc5_dt_decl_add_constructor(list, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(list, nil);

  std::vector<Cvc5DatatypeDecl> dtdecls{tree, list};
  const Cvc5Sort* dtsorts =
      cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  for (size_t i = 0, size = dtdecls.size(); i < size; i++)
  {
    ASSERT_TRUE(cvc5_sort_is_dt(dtsorts[i]));
    ASSERT_FALSE(cvc5_dt_is_finite(cvc5_sort_get_datatype(dtsorts[i])));
    ASSERT_EQ(std::string(cvc5_dt_get_name(cvc5_sort_get_datatype(dtsorts[i]))),
              cvc5_dt_decl_get_name(dtdecls[i]));
  }

  // verify the resolution was correct
  Cvc5Datatype dt_tree = cvc5_sort_get_datatype(dtsorts[0]);
  Cvc5DatatypeConstructor dt_tree_node = cvc5_dt_get_constructor(dt_tree, 0);
  ASSERT_EQ(cvc5_dt_cons_get_name(dt_tree_node), std::string("node"));
  Cvc5DatatypeSelector dt_tree_node_left =
      cvc5_dt_cons_get_selector(dt_tree_node, 0);
  ASSERT_EQ(cvc5_dt_sel_get_name(dt_tree_node_left), std::string("left"));
  // argument type should have resolved to be recursive
  ASSERT_TRUE(
      cvc5_sort_is_dt(cvc5_dt_sel_get_codomain_sort(dt_tree_node_left)));
  ASSERT_TRUE(cvc5_sort_is_equal(
      cvc5_dt_sel_get_codomain_sort(dt_tree_node_left), dtsorts[0]));
}

TEST_F(TestCApiBlackDatatype, datatype_structs)
{
  // create datatype sort to test
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", d_int);
  cvc5_dt_cons_decl_add_selector_self(cons, "tail");

  ASSERT_DEATH(cvc5_dt_cons_decl_add_selector(cons, "head", nullptr),
               "invalid sort");
  ;

  cvc5_dt_decl_add_constructor(decl, cons);

  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);

  Cvc5Sort dt_sort = cvc5_mk_dt_sort(d_tm, decl);
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sort);
  ASSERT_FALSE(cvc5_dt_is_codatatype(dt));
  ASSERT_FALSE(cvc5_dt_is_tuple(dt));
  ASSERT_FALSE(cvc5_dt_is_record(dt));
  ASSERT_FALSE(cvc5_dt_is_finite(dt));
  ASSERT_TRUE(cvc5_dt_is_well_founded(dt));
  // get constructor
  Cvc5DatatypeConstructor dt_cons = cvc5_dt_get_constructor(dt, 0);
  (void)cvc5_dt_cons_get_term(dt_cons);
  ASSERT_EQ(cvc5_dt_cons_get_num_selectors(dt_cons), 2);

  // create datatype sort to test
  Cvc5DatatypeDecl decl_enum = cvc5_mk_dt_decl(d_tm, "enum", false);
  Cvc5DatatypeConstructorDecl ca = cvc5_mk_dt_cons_decl(d_tm, "A");
  Cvc5DatatypeConstructorDecl cb = cvc5_mk_dt_cons_decl(d_tm, "B");
  Cvc5DatatypeConstructorDecl cc = cvc5_mk_dt_cons_decl(d_tm, "C");
  cvc5_dt_decl_add_constructor(decl_enum, ca);
  cvc5_dt_decl_add_constructor(decl_enum, cb);
  cvc5_dt_decl_add_constructor(decl_enum, cc);

  Cvc5Sort dt_enum_sort = cvc5_mk_dt_sort(d_tm, decl_enum);
  Cvc5Datatype dt_enum = cvc5_sort_get_datatype(dt_enum_sort);
  ASSERT_FALSE(cvc5_dt_is_tuple(dt_enum));
  ASSERT_TRUE(cvc5_dt_is_finite(dt_enum));

  // create codatatype
  Cvc5DatatypeDecl decl_stream = cvc5_mk_dt_decl(d_tm, "stream", true);
  Cvc5DatatypeConstructorDecl cons_stream = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons_stream, "head", d_int);
  cvc5_dt_cons_decl_add_selector_self(cons_stream, "tail");
  cvc5_dt_decl_add_constructor(decl_stream, cons_stream);

  Cvc5Sort dt_stream_sort = cvc5_mk_dt_sort(d_tm, decl_stream);
  Cvc5Datatype dt_stream = cvc5_sort_get_datatype(dt_stream_sort);
  ASSERT_TRUE(cvc5_dt_is_codatatype(dt_stream));
  ASSERT_FALSE(cvc5_dt_is_finite(dt_stream));
  // codatatypes may be well-founded
  ASSERT_TRUE(cvc5_dt_is_well_founded(dt_stream));

  // create tuple
  std::vector<Cvc5Sort> elem_sorts = {d_bool};
  Cvc5Sort tup_sort =
      cvc5_mk_tuple_sort(d_tm, elem_sorts.size(), elem_sorts.data());
  Cvc5Datatype dt_tuple = cvc5_sort_get_datatype(tup_sort);
  ASSERT_TRUE(cvc5_dt_is_tuple(dt_tuple));
  ASSERT_FALSE(cvc5_dt_is_record(dt_tuple));
  ASSERT_TRUE(cvc5_dt_is_finite(dt_tuple));
  ASSERT_TRUE(cvc5_dt_is_well_founded(dt_tuple));

  // create record
  std::vector<const char*> names = {"b", "i"};
  std::vector<Cvc5Sort> sorts = {d_bool, d_int};
  Cvc5Sort rec_sort =
      cvc5_mk_record_sort(d_tm, names.size(), names.data(), sorts.data());
  ASSERT_TRUE(cvc5_sort_is_dt(rec_sort));
  Cvc5Datatype dt_record = cvc5_sort_get_datatype(rec_sort);
  ASSERT_FALSE(cvc5_dt_is_record(dt_tuple));
  ASSERT_TRUE(cvc5_dt_is_record(dt_record));
  ASSERT_FALSE(cvc5_dt_is_finite(dt_record));
  ASSERT_TRUE(cvc5_dt_is_well_founded(dt_record));
}

TEST_F(TestCApiBlackDatatype, datatype_names)
{
  // create datatype sort to test
  Cvc5DatatypeDecl list = cvc5_mk_dt_decl(d_tm, "list", false);
  ASSERT_EQ(cvc5_dt_decl_get_name(list), std::string("list"));

  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", d_int);
  cvc5_dt_cons_decl_add_selector_self(cons, "tail");
  cvc5_dt_decl_add_constructor(list, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(list, nil);

  Cvc5Sort dt_sort = cvc5_mk_dt_sort(d_tm, list);
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sort);
  size_t size;
  ASSERT_DEATH(cvc5_dt_get_parameters(dt, &size),
               "expected parametric datatype");
  ASSERT_EQ(cvc5_dt_get_name(dt), std::string("list"));
  (void)cvc5_dt_get_constructor_by_name(dt, "nil");
  (void)cvc5_dt_get_constructor_by_name(dt, "cons");
  ASSERT_DEATH(cvc5_dt_get_constructor_by_name(dt, "head"),
               "no constructor head");
  ASSERT_DEATH(cvc5_dt_get_constructor_by_name(dt, ""), "no constructor");

  Cvc5DatatypeConstructor dt_cons = cvc5_dt_get_constructor(dt, 0);
  ASSERT_EQ(cvc5_dt_cons_get_name(dt_cons), std::string("cons"));
  (void)cvc5_dt_cons_get_selector_by_name(dt_cons, "head");
  (void)cvc5_dt_cons_get_selector_by_name(dt_cons, "tail");
  ASSERT_DEATH(cvc5_dt_cons_get_selector_by_name(dt_cons, "cons"),
               "no selector");

  // get selector
  Cvc5DatatypeSelector dt_sel_tail = cvc5_dt_cons_get_selector(dt_cons, 1);
  ASSERT_EQ(cvc5_dt_sel_get_name(dt_sel_tail), std::string("tail"));
  ASSERT_TRUE(
      cvc5_sort_is_equal(cvc5_dt_sel_get_codomain_sort(dt_sel_tail), dt_sort));

  // get selector from datatype
  (void)cvc5_dt_get_selector(dt, "head");
  ASSERT_DEATH(cvc5_dt_get_selector(dt, "cons"), "no selector");

  ASSERT_DEATH(cvc5_dt_decl_get_name(nullptr), "invalid datatype declaration");
  ASSERT_DEATH(cvc5_dt_get_name(nullptr), "invalid datatype");
  ASSERT_DEATH(cvc5_dt_cons_get_name(nullptr), "invalid datatype constructor");
  ASSERT_DEATH(cvc5_dt_sel_get_name(nullptr), "invalid datatype selector");
}

TEST_F(TestCApiBlackDatatype, parametric_datatype)
{
  Cvc5Sort t1 = cvc5_mk_param_sort(d_tm, "T1");
  Cvc5Sort t2 = cvc5_mk_param_sort(d_tm, "T2");
  std::vector<Cvc5Sort> v{t1, t2};
  Cvc5DatatypeDecl decl_pair =
      cvc5_mk_dt_decl_with_params(d_tm, "pair", v.size(), v.data(), false);
  Cvc5DatatypeConstructorDecl mkpair = cvc5_mk_dt_cons_decl(d_tm, "mk-pair");
  cvc5_dt_cons_decl_add_selector(mkpair, "first", t1);
  cvc5_dt_cons_decl_add_selector(mkpair, "second", t2);
  cvc5_dt_decl_add_constructor(decl_pair, mkpair);

  Cvc5Sort pair_sort = cvc5_mk_dt_sort(d_tm, decl_pair);
  Cvc5Datatype dt_pair = cvc5_sort_get_datatype(pair_sort);
  ASSERT_TRUE(cvc5_dt_is_parametric(dt_pair));
  size_t size;
  const Cvc5Sort* params = cvc5_dt_get_parameters(dt_pair, &size);
  ASSERT_TRUE(cvc5_sort_is_equal(params[0], t1)
              && cvc5_sort_is_equal(params[1], t2));

  v = {d_int, d_int};
  Cvc5Sort pair_int_int = cvc5_sort_instantiate(pair_sort, v.size(), v.data());
  v = {d_real, d_real};
  Cvc5Sort pair_real_real =
      cvc5_sort_instantiate(pair_sort, v.size(), v.data());
  v = {d_real, d_int};
  Cvc5Sort pair_real_int = cvc5_sort_instantiate(pair_sort, v.size(), v.data());
  v = {d_int, d_real};
  Cvc5Sort pair_int_real = cvc5_sort_instantiate(pair_sort, v.size(), v.data());

  ASSERT_FALSE(cvc5_sort_is_equal(pair_int_int, pair_real_real));
  ASSERT_FALSE(cvc5_sort_is_equal(pair_int_real, pair_real_real));
  ASSERT_FALSE(cvc5_sort_is_equal(pair_real_int, pair_real_real));
  ASSERT_FALSE(cvc5_sort_is_equal(pair_int_int, pair_int_real));
  ASSERT_FALSE(cvc5_sort_is_equal(pair_int_int, pair_real_int));
  ASSERT_FALSE(cvc5_sort_is_equal(pair_int_real, pair_real_int));

  ASSERT_DEATH(
      cvc5_mk_dt_decl_with_params(nullptr, "pair", v.size(), v.data(), false),
      "unexpected NULL argument");
  v = {};
  (void)cvc5_mk_dt_decl_with_params(d_tm, "some", v.size(), v.data(), false);
  (void)cvc5_mk_dt_decl_with_params(d_tm, "some", v.size(), nullptr, false);
  v = {nullptr};
  ASSERT_DEATH(
      cvc5_mk_dt_decl_with_params(d_tm, "pair", v.size(), v.data(), false),
      "invalid sort at index 0");
}

TEST_F(TestCApiBlackDatatype, is_finite)
{
  std::vector<Cvc5Sort> v;
  Cvc5DatatypeDecl decl =
      cvc5_mk_dt_decl_with_params(d_tm, "dt", v.size(), v.data(), false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "sel", d_bool);
  cvc5_dt_decl_add_constructor(decl, cons);

  Cvc5Sort dt_sort = cvc5_mk_dt_sort(d_tm, decl);
  ASSERT_TRUE(cvc5_dt_is_finite(cvc5_sort_get_datatype(dt_sort)));

  Cvc5Sort p = cvc5_mk_param_sort(d_tm, "p1");
  v = {p};
  Cvc5DatatypeDecl pdecl =
      cvc5_mk_dt_decl_with_params(d_tm, "dt", v.size(), v.data(), false);
  Cvc5DatatypeConstructorDecl pcons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(pcons, "sel", p);
  cvc5_dt_decl_add_constructor(pdecl, pcons);

  ASSERT_DEATH(cvc5_dt_is_finite(nullptr), "invalid datatype");

  Cvc5Sort pdt_sort = cvc5_mk_dt_sort(d_tm, pdecl);
  ASSERT_DEATH(cvc5_dt_is_finite(cvc5_sort_get_datatype(pdt_sort)),
               "expected non-parametric datatype");
}

TEST_F(TestCApiBlackDatatype, datatype_simply_rec)
{
  /* Create mutual datatypes corresponding to this definition block:
   *
   *   DATATYPE
   *     wlist = leaf(data: list),
   *     list = cons(car: wlist, cdr: list) | nil,
   *     ns = elem(ndata: set(wlist)) | elemArray(ndata2: array(list, list))
   *   END;
   */
  // Make unresolved types as placeholders

  // Sort unresWList = d_tm.mkUnresolvedDatatypeSort("wlist");
  Cvc5Sort unres_wlist = cvc5_mk_unresolved_dt_sort(d_tm, "wlist", 0);
  // Sort unresList = d_tm.mkUnresolvedDatatypeSort("list");
  Cvc5Sort unres_list = cvc5_mk_unresolved_dt_sort(d_tm, "list", 0);

  // DatatypeDecl wlist = d_tm.mkDatatypeDecl("wlist");
  Cvc5DatatypeDecl wlist = cvc5_mk_dt_decl(d_tm, "wlist", false);
  // DatatypeConstructorDecl leaf = d_tm.mkDatatypeConstructorDecl("leaf");
  Cvc5DatatypeConstructorDecl leaf = cvc5_mk_dt_cons_decl(d_tm, "leaf");
  // leaf.addSelector("data", unresList);
  cvc5_dt_cons_decl_add_selector(leaf, "data", unres_list);
  // wlist.addConstructor(leaf);
  cvc5_dt_decl_add_constructor(wlist, leaf);

  // DatatypeDecl list = d_tm.mkDatatypeDecl("list");
  Cvc5DatatypeDecl list = cvc5_mk_dt_decl(d_tm, "list", false);
  // DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  // DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  // cons.addSelector("car", unresWList);
  cvc5_dt_cons_decl_add_selector(cons, "car", unres_wlist);
  // cons.addSelector("cdr", unresList);
  cvc5_dt_cons_decl_add_selector(cons, "cdr", unres_list);
  // list.addConstructor(cons);
  cvc5_dt_decl_add_constructor(list, cons);
  // list.addConstructor(nil);
  cvc5_dt_decl_add_constructor(list, nil);

  // DatatypeDecl ns = d_tm.mkDatatypeDecl("ns");
  Cvc5DatatypeDecl ns = cvc5_mk_dt_decl(d_tm, "ns", false);
  // DatatypeConstructorDecl elem = d_tm.mkDatatypeConstructorDecl("elem");
  Cvc5DatatypeConstructorDecl elem = cvc5_mk_dt_cons_decl(d_tm, "elem");
  // elem.addSelector("ndata", d_tm.mkSetSort(unresWList));
  cvc5_dt_cons_decl_add_selector(
      elem, "ndata", cvc5_mk_set_sort(d_tm, unres_wlist));
  // ns.addConstructor(elem);
  cvc5_dt_decl_add_constructor(ns, elem);
  // DatatypeConstructorDecl elemArray =
  //     d_tm.mkDatatypeConstructorDecl("elemArray");
  Cvc5DatatypeConstructorDecl elem_array =
      cvc5_mk_dt_cons_decl(d_tm, "elem_array");
  // elemArray.addSelector("ndata", d_tm.mkArraySort(unresList, unresList));
  cvc5_dt_cons_decl_add_selector(
      elem_array, "ndata", cvc5_mk_array_sort(d_tm, unres_list, unres_list));
  // ns.addConstructor(elemArray);
  cvc5_dt_decl_add_constructor(ns, elem_array);

  std::vector<Cvc5DatatypeDecl> dtdecls{wlist, list, ns};
  // this is well-founded and has no nested recursion
  const Cvc5Sort* dt_sorts =
      cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dt_sorts[0])));
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dt_sorts[1])));
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dt_sorts[2])));

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     ns2 = elem2(ndata: array(int,ns2)) | nil2
   *   END;
   */
  Cvc5Sort unres_ns2 = cvc5_mk_unresolved_dt_sort(d_tm, "ns2", 0);
  Cvc5DatatypeDecl ns2 = cvc5_mk_dt_decl(d_tm, "ns2", false);
  Cvc5DatatypeConstructorDecl elem2 = cvc5_mk_dt_cons_decl(d_tm, "elem2");
  cvc5_dt_cons_decl_add_selector(
      elem2, "ndata", cvc5_mk_array_sort(d_tm, d_int, unres_ns2));
  cvc5_dt_decl_add_constructor(ns2, elem2);
  Cvc5DatatypeConstructorDecl nil2 = cvc5_mk_dt_cons_decl(d_tm, "nil2");
  cvc5_dt_decl_add_constructor(ns2, nil2);

  dtdecls = {ns2};
  // this is not well-founded due to non-simple recursion
  cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  Cvc5Datatype dt = cvc5_sort_get_datatype(dt_sorts[0]);
  Cvc5DatatypeConstructor c = cvc5_dt_get_constructor(dt, 0);
  Cvc5DatatypeSelector s = cvc5_dt_cons_get_selector(c, 0);
  Cvc5Sort codomain = cvc5_dt_sel_get_codomain_sort(s);
  ASSERT_TRUE(cvc5_sort_is_array(codomain));
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_sort_array_get_element_sort(codomain),
                                 dt_sorts[0]));
  ASSERT_TRUE(cvc5_dt_is_well_founded(dt));

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list3 = cons3(car: ns3, cdr: list3) | nil3,
   *     ns3 = elem3(ndata: set(list3))
   *   END;
   */
  Cvc5Sort unres_ns3 = cvc5_mk_unresolved_dt_sort(d_tm, "ns3", 0);
  Cvc5Sort unres_list3 = cvc5_mk_unresolved_dt_sort(d_tm, "list3", 0);

  Cvc5DatatypeDecl list3 = cvc5_mk_dt_decl(d_tm, "list3", false);
  Cvc5DatatypeConstructorDecl cons3 = cvc5_mk_dt_cons_decl(d_tm, "cons3");
  cvc5_dt_cons_decl_add_selector(cons3, "car", unres_ns3);
  cvc5_dt_cons_decl_add_selector(cons3, "cdr", unres_list3);
  cvc5_dt_decl_add_constructor(list3, cons3);
  Cvc5DatatypeConstructorDecl nil3 = cvc5_mk_dt_cons_decl(d_tm, "nil3");
  cvc5_dt_decl_add_constructor(list3, nil3);

  Cvc5DatatypeDecl ns3 = cvc5_mk_dt_decl(d_tm, "ns3", false);
  Cvc5DatatypeConstructorDecl elem3 = cvc5_mk_dt_cons_decl(d_tm, "elem3");
  cvc5_dt_cons_decl_add_selector(
      elem3, "ndata", cvc5_mk_set_sort(d_tm, unres_list3));
  cvc5_dt_decl_add_constructor(ns3, elem3);

  dtdecls = {list3, ns3};
  // both are well-founded and have nested recursion
  const Cvc5Sort* dtsorts =
      cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dtsorts[0])));
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dtsorts[1])));

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list4 = cons(car: set(ns4), cdr: list4) | nil,
   *     ns4 = elem(ndata: list4)
   *   END;
   */
  Cvc5Sort unres_ns4 = cvc5_mk_unresolved_dt_sort(d_tm, "ns4", 0);
  Cvc5Sort unres_list4 = cvc5_mk_unresolved_dt_sort(d_tm, "list4", 0);

  Cvc5DatatypeDecl list4 = cvc5_mk_dt_decl(d_tm, "list4", false);
  Cvc5DatatypeConstructorDecl cons4 = cvc5_mk_dt_cons_decl(d_tm, "cons4");
  cvc5_dt_cons_decl_add_selector(
      cons4, "car", cvc5_mk_set_sort(d_tm, unres_ns4));
  cvc5_dt_cons_decl_add_selector(cons4, "cdr", unres_list4);
  cvc5_dt_decl_add_constructor(list4, cons4);
  Cvc5DatatypeConstructorDecl nil4 = cvc5_mk_dt_cons_decl(d_tm, "nil4");
  cvc5_dt_decl_add_constructor(list4, nil4);

  Cvc5DatatypeDecl ns4 = cvc5_mk_dt_decl(d_tm, "ns4", false);
  Cvc5DatatypeConstructorDecl elem4 = cvc5_mk_dt_cons_decl(d_tm, "elem4");
  cvc5_dt_cons_decl_add_selector(elem4, "ndata", unres_list4);
  cvc5_dt_decl_add_constructor(ns4, elem4);

  dtdecls = {list4, ns4};

  // both are well-founded and have nested recursion
  dtsorts = cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dtsorts[0])));
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dtsorts[1])));

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
   *   END;
   */
  Cvc5Sort unres_list5 =
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 1, "list5");
  Cvc5Sort x = cvc5_mk_param_sort(d_tm, "X");
  std::vector<Cvc5Sort> v = {x};

  Cvc5DatatypeDecl list5 =
      cvc5_mk_dt_decl_with_params(d_tm, "list5", v.size(), v.data(), false);
  std::vector<Cvc5Sort> args{x};
  args = {cvc5_sort_instantiate(unres_list5, args.size(), args.data())};
  Cvc5Sort ur_list_listx =
      cvc5_sort_instantiate(unres_list5, args.size(), args.data());

  Cvc5DatatypeConstructorDecl cons5 = cvc5_mk_dt_cons_decl(d_tm, "cons5");
  cvc5_dt_cons_decl_add_selector(cons5, "car", x);
  cvc5_dt_cons_decl_add_selector(cons5, "cdr", ur_list_listx);
  cvc5_dt_decl_add_constructor(list5, cons5);
  Cvc5DatatypeConstructorDecl nil5 = cvc5_mk_dt_cons_decl(d_tm, "nil5");
  cvc5_dt_decl_add_constructor(list5, nil5);

  dtdecls = {list5};
  // well-founded and has nested recursion
  dtsorts = cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  ASSERT_TRUE(cvc5_dt_is_well_founded(cvc5_sort_get_datatype(dtsorts[0])));
}

TEST_F(TestCApiBlackDatatype, datatype_specialized_cons)
{
  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     plist[X] = pcons(car: X, cdr: plist[X]) | pnil
   *   END;
   */
  // Make unresolved types as placeholders
  Cvc5Sort unres_list =
      cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 1, "plist");

  Cvc5Sort x = cvc5_mk_param_sort(d_tm, "X");
  std::vector<Cvc5Sort> v{x};
  Cvc5DatatypeDecl plist =
      cvc5_mk_dt_decl_with_params(d_tm, "plist", v.size(), v.data(), false);

  std::vector<Cvc5Sort> args{x};
  Cvc5Sort ur_listx =
      cvc5_sort_instantiate(unres_list, args.size(), args.data());

  Cvc5DatatypeConstructorDecl pcons = cvc5_mk_dt_cons_decl(d_tm, "pcons");
  cvc5_dt_cons_decl_add_selector(pcons, "car", x);
  cvc5_dt_cons_decl_add_selector(pcons, "cdr", ur_listx);
  cvc5_dt_decl_add_constructor(plist, pcons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "pnilcons");
  cvc5_dt_decl_add_constructor(plist, nil);

  std::vector<Cvc5DatatypeDecl> dtdecls{plist};
  // make the datatype sorts
  const Cvc5Sort* dtsorts =
      cvc5_mk_dt_sorts(d_tm, dtdecls.size(), dtdecls.data());
  Cvc5Datatype dt = cvc5_sort_get_datatype(dtsorts[0]);
  Cvc5DatatypeConstructor nilc = cvc5_dt_get_constructor(dt, 0);

  std::vector<Cvc5Sort> iargs{d_int};
  Cvc5Sort list_int =
      cvc5_sort_instantiate(dtsorts[0], iargs.size(), iargs.data());

  size_t size;
  const Cvc5Sort* list_int_params =
      cvc5_dt_get_parameters(cvc5_sort_get_datatype(list_int), &size);
  // the parameter of the datatype is not instantiated
  ASSERT_TRUE(size == 1 && cvc5_sort_is_equal(list_int_params[0], x));

  Cvc5Term cons_term = cvc5_dt_cons_get_instantiated_term(nilc, list_int);
  // get the specialized constructor term for list[Int]
  ASSERT_TRUE(cvc5_term_is_disequal(cons_term, cvc5_dt_cons_get_term(nilc)));
  // error to get the specialized constructor term for Int
  ASSERT_DEATH(cvc5_dt_cons_get_instantiated_term(nilc, d_int),
               "cannot get specialized constructor");
}
}  // namespace cvc5::internal::test
