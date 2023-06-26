/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::BooleanSimplification.
 */

#include <algorithm>
#include <set>
#include <vector>

#include "expr/kind.h"
#include "expr/node.h"
#include "options/io_utils.h"
#include "options/language.h"
#include "preprocessing/util/boolean_simplification.h"
#include "test_node.h"

using namespace cvc5::internal::preprocessing;

namespace cvc5::internal {
namespace test {

class TestUtilBlackBooleanSimplification : public TestNode
{
 protected:
  void SetUp() override
  {
    TestNode::SetUp();

    d_a = d_skolemManager->mkDummySkolem("a", d_nodeManager->booleanType());
    d_b = d_skolemManager->mkDummySkolem("b", d_nodeManager->booleanType());
    d_c = d_skolemManager->mkDummySkolem("c", d_nodeManager->booleanType());
    d_d = d_skolemManager->mkDummySkolem("d", d_nodeManager->booleanType());
    d_e = d_skolemManager->mkDummySkolem("e", d_nodeManager->booleanType());
    d_f = d_skolemManager->mkDummySkolem(
        "f",
        d_nodeManager->mkFunctionType(d_nodeManager->booleanType(),
                                      d_nodeManager->booleanType()));
    d_g = d_skolemManager->mkDummySkolem(
        "g",
        d_nodeManager->mkFunctionType(d_nodeManager->booleanType(),
                                      d_nodeManager->booleanType()));
    d_h = d_skolemManager->mkDummySkolem(
        "h",
        d_nodeManager->mkFunctionType(d_nodeManager->booleanType(),
                                      d_nodeManager->booleanType()));
    d_fa = d_nodeManager->mkNode(kind::APPLY_UF, d_f, d_a);
    d_fb = d_nodeManager->mkNode(kind::APPLY_UF, d_f, d_b);
    d_fc = d_nodeManager->mkNode(kind::APPLY_UF, d_f, d_c);
    d_ga = d_nodeManager->mkNode(kind::APPLY_UF, d_g, d_a);
    d_ha = d_nodeManager->mkNode(kind::APPLY_UF, d_h, d_a);
    d_hc = d_nodeManager->mkNode(kind::APPLY_UF, d_h, d_c);
    d_ffb = d_nodeManager->mkNode(kind::APPLY_UF, d_f, d_fb);
    d_fhc = d_nodeManager->mkNode(kind::APPLY_UF, d_f, d_hc);
    d_hfc = d_nodeManager->mkNode(kind::APPLY_UF, d_h, d_fc);
    d_gfb = d_nodeManager->mkNode(kind::APPLY_UF, d_g, d_fb);

    d_ac = d_nodeManager->mkNode(kind::EQUAL, d_a, d_c);
    d_ffbd = d_nodeManager->mkNode(kind::EQUAL, d_ffb, d_d);
    d_efhc = d_nodeManager->mkNode(kind::EQUAL, d_e, d_fhc);
    d_dfa = d_nodeManager->mkNode(kind::EQUAL, d_d, d_fa);

    // this test is designed for >= 10 removal threshold
    Assert(BooleanSimplification::DUPLICATE_REMOVAL_THRESHOLD >= 10);

    options::ioutils::applyNodeDepth(std::cout, -1);
    options::ioutils::applyOutputLanguage(std::cout,
                                          Language::LANG_SMTLIB_V2_6);
  }

  // assert equality up to commuting children
  void test_nodes_equal(TNode n1, TNode n2)
  {
    std::cout << "ASSERTING: " << n1 << std::endl
              << "        ~= " << n2 << std::endl;
    ASSERT_EQ(n1.getKind(), n2.getKind());
    ASSERT_EQ(n1.getNumChildren(), n2.getNumChildren());
    std::vector<TNode> v1(n1.begin(), n1.end());
    std::vector<TNode> v2(n2.begin(), n2.end());
    sort(v1.begin(), v1.end());
    sort(v2.begin(), v2.end());
    ASSERT_EQ(v1, v2);
  }

  // assert that node's children have same elements as the set
  // (so no duplicates); also n is asserted to have kind k
  void test_node_equals_set(TNode n, Kind k, std::set<TNode> elts)
  {
    std::vector<TNode> v(n.begin(), n.end());

    // BooleanSimplification implementation sorts its output nodes, BUT
    // that's an implementation detail, not part of the contract, so we
    // should be robust to it here; this is a black-box test!
    sort(v.begin(), v.end());

    ASSERT_EQ(n.getKind(), k);
    ASSERT_EQ(elts.size(), n.getNumChildren());
    ASSERT_TRUE(equal(n.begin(), n.end(), elts.begin()));
  }

  Node d_a, d_b, d_c, d_d, d_e, d_f, d_g, d_h;
  Node d_fa, d_fb, d_fc, d_ga, d_ha, d_hc, d_ffb, d_fhc, d_hfc, d_gfb;
  Node d_ac, d_ffbd, d_efhc, d_dfa;
};

TEST_F(TestUtilBlackBooleanSimplification, negate)
{
  Node in, out;

  in = d_nodeManager->mkNode(kind::NOT, d_a);
  out = d_a;
  test_nodes_equal(out, BooleanSimplification::negate(in));
  test_nodes_equal(in, BooleanSimplification::negate(out));

  in = d_fa.andNode(d_ac).notNode().notNode().notNode().notNode();
  out = d_fa.andNode(d_ac).notNode();
  test_nodes_equal(out, BooleanSimplification::negate(in));

#ifdef CVC5_ASSERTIONS
  in = Node();
  ASSERT_THROW(BooleanSimplification::negate(in), AssertArgumentException);
#endif
}

TEST_F(TestUtilBlackBooleanSimplification, simplifyClause)
{
  Node in, out;

  in = d_a.orNode(d_b);
  out = in;
  test_nodes_equal(out, BooleanSimplification::simplifyClause(in));

  in = d_nodeManager->mkNode(kind::OR, d_a, d_d.andNode(d_b));
  out = in;
  test_nodes_equal(out, BooleanSimplification::simplifyClause(in));

  in = d_nodeManager->mkNode(kind::OR, d_a, d_d.orNode(d_b));
  out = d_nodeManager->mkNode(kind::OR, d_a, d_d, d_b);
  test_nodes_equal(out, BooleanSimplification::simplifyClause(in));

  in = d_nodeManager->mkNode(
      kind::OR,
      {d_fa, d_ga.orNode(d_c).notNode(), d_hfc, d_ac, d_d.andNode(d_b)});
  out = NodeBuilder(kind::OR) << d_fa << d_ga.orNode(d_c).notNode() << d_hfc
                              << d_ac << d_d.andNode(d_b);
  test_nodes_equal(out, BooleanSimplification::simplifyClause(in));

  in = d_nodeManager->mkNode(
      kind::OR,
      {d_fa, d_ga.andNode(d_c).notNode(), d_hfc, d_ac, d_d.andNode(d_b)});
  out = NodeBuilder(kind::OR) << d_fa << d_ga.notNode() << d_c.notNode()
                              << d_hfc << d_ac << d_d.andNode(d_b);
  test_nodes_equal(out, BooleanSimplification::simplifyClause(in));

#ifdef CVC5_ASSERTIONS
  in = d_nodeManager->mkNode(kind::AND, d_a, d_b);
  ASSERT_THROW(BooleanSimplification::simplifyClause(in),
               AssertArgumentException);
#endif
}

TEST_F(TestUtilBlackBooleanSimplification, simplifyHornClause)
{
  Node in, out;

  in = d_a.impNode(d_b);
  out = d_a.notNode().orNode(d_b);
  test_nodes_equal(out, BooleanSimplification::simplifyHornClause(in));

  in = d_a.notNode().impNode(d_ac.andNode(d_b));
  out = d_nodeManager->mkNode(kind::OR, d_a, d_ac.andNode(d_b));
  test_nodes_equal(out, BooleanSimplification::simplifyHornClause(in));

  in = d_a.andNode(d_b).impNode(
      d_nodeManager->mkNode(kind::AND,
                            {d_fa,
                             d_ga.orNode(d_c).notNode(),
                             d_hfc.orNode(d_ac),
                             d_d.andNode(d_b)}));
  out = d_nodeManager->mkNode(kind::OR,
                              d_a.notNode(),
                              d_b.notNode(),
                              d_nodeManager->mkNode(kind::AND,
                                                    {d_fa,
                                                     d_ga.orNode(d_c).notNode(),
                                                     d_hfc.orNode(d_ac),
                                                     d_d.andNode(d_b)}));
  test_nodes_equal(out, BooleanSimplification::simplifyHornClause(in));

  in = d_a.andNode(d_b).impNode(
      d_nodeManager->mkNode(kind::OR,
                            {d_fa,
                             d_ga.orNode(d_c).notNode(),
                             d_hfc.orNode(d_ac),
                             d_d.andNode(d_b).notNode()}));
  out = NodeBuilder(kind::OR)
        << d_a.notNode() << d_b.notNode() << d_fa << d_ga.orNode(d_c).notNode()
        << d_hfc << d_ac << d_d.notNode();
  test_nodes_equal(out, BooleanSimplification::simplifyHornClause(in));

#ifdef CVC5_ASSERTIONS
  in = d_nodeManager->mkNode(kind::OR, d_a, d_b);
  ASSERT_THROW(BooleanSimplification::simplifyHornClause(in),
               AssertArgumentException);
#endif
}

TEST_F(TestUtilBlackBooleanSimplification, simplifyConflict)
{
  Node in, out;

  in = d_a.andNode(d_b);
  out = in;
  test_nodes_equal(out, BooleanSimplification::simplifyConflict(in));

  in = d_nodeManager->mkNode(kind::AND, d_a, d_d.andNode(d_b));
  out = d_nodeManager->mkNode(kind::AND, d_a, d_d, d_b);
  test_nodes_equal(out, BooleanSimplification::simplifyConflict(in));

  in = d_nodeManager->mkNode(kind::AND,
                             {d_fa,
                              d_ga.orNode(d_c).notNode(),
                              d_fa,
                              d_hfc.orNode(d_ac),
                              d_d.andNode(d_b)});
  out = NodeBuilder(kind::AND) << d_fa << d_ga.notNode() << d_c.notNode()
                               << d_hfc.orNode(d_ac) << d_d << d_b;
  test_nodes_equal(out, BooleanSimplification::simplifyConflict(in));

#ifdef CVC5_ASSERTIONS
  in = d_nodeManager->mkNode(kind::OR, d_a, d_b);
  ASSERT_THROW(BooleanSimplification::simplifyConflict(in),
               AssertArgumentException);
#endif
}
}  // namespace test
}  // namespace cvc5::internal
