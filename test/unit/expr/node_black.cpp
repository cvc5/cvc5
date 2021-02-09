/*********************                                                        */
/*! \file node_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Node.
 **
 ** Black box testing of CVC4::Node.
 **/

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "api/cvc4cpp.h"
#include "expr/dtype.h"
#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"
#include "smt/smt_engine.h"
#include "test_node.h"
#include "theory/rewriter.h"

namespace CVC4 {

using namespace kind;

namespace test {

namespace {
/** Returns N skolem nodes from 'nodeManager' with the same `type`. */
std::vector<Node> makeNSkolemNodes(NodeManager* nodeManager,
                                   uint32_t n,
                                   TypeNode type)
{
  std::vector<Node> skolems;
  for (uint32_t i = 0; i < n; i++)
  {
    skolems.push_back(nodeManager->mkSkolem(
        "skolem_", type, "Created by makeNSkolemNodes()"));
  }
  return skolems;
}
}  // namespace

class TestNodeBlackNode : public TestNodeBlack
{
 protected:
  void SetUp() override
  {
    TestNodeBlack::SetUp();
    // setup an SMT engine so that options are in scope
    Options opts;
    char* argv[2];
    argv[0] = strdup("");
    argv[1] = strdup("--output-lang=ast");
    Options::parseOptions(&opts, 2, argv);
    free(argv[0]);
    free(argv[1]);
    d_smt.reset(new SmtEngine(d_nodeManager.get(), &opts));
  }

  std::unique_ptr<SmtEngine> d_smt;

  bool imp(bool a, bool b) const { return (!a) || (b); }
  bool iff(bool a, bool b) const { return (a && b) || ((!a) && (!b)); }

  void testNaryExpForSize(Kind k, uint32_t n)
  {
    NodeBuilder<> nbz(k);
    Node trueNode = d_nodeManager->mkConst(true);
    for (uint32_t i = 0; i < n; ++i)
    {
      nbz << trueNode;
    }
    Node result = nbz;
    ASSERT_EQ(n, result.getNumChildren());
  }
};

TEST_F(TestNodeBlackNode, null) { Node::null(); }

TEST_F(TestNodeBlackNode, is_null)
{
  Node a = Node::null();
  ASSERT_TRUE(a.isNull());

  Node b = Node();
  ASSERT_TRUE(b.isNull());

  Node c = b;
  ASSERT_TRUE(c.isNull());
}

TEST_F(TestNodeBlackNode, copy_ctor) { Node e(Node::null()); }

TEST_F(TestNodeBlackNode, dtor)
{
  /* No access to internals? Only test that this is crash free. */
  Node* n;
  ASSERT_NO_FATAL_FAILURE(n = new Node());
  delete n;
}

/* operator== */
TEST_F(TestNodeBlackNode, operator_equals)
{
  Node a, b, c;

  b = d_nodeManager->mkSkolem("b", d_nodeManager->booleanType());

  a = b;
  c = a;

  Node d = d_nodeManager->mkSkolem("d", d_nodeManager->booleanType());

  ASSERT_TRUE(a == a);
  ASSERT_TRUE(a == b);
  ASSERT_TRUE(a == c);

  ASSERT_TRUE(b == a);
  ASSERT_TRUE(b == b);
  ASSERT_TRUE(b == c);

  ASSERT_TRUE(c == a);
  ASSERT_TRUE(c == b);
  ASSERT_TRUE(c == c);

  ASSERT_TRUE(d == d);

  ASSERT_FALSE(d == a);
  ASSERT_FALSE(d == b);
  ASSERT_FALSE(d == c);

  ASSERT_FALSE(a == d);
  ASSERT_FALSE(b == d);
  ASSERT_FALSE(c == d);
}

/* operator!= */
TEST_F(TestNodeBlackNode, operator_not_equals)
{
  Node a, b, c;

  b = d_nodeManager->mkSkolem("b", d_nodeManager->booleanType());

  a = b;
  c = a;

  Node d = d_nodeManager->mkSkolem("d", d_nodeManager->booleanType());

  /*structed assuming operator == works */
  ASSERT_TRUE(iff(a != a, !(a == a)));
  ASSERT_TRUE(iff(a != b, !(a == b)));
  ASSERT_TRUE(iff(a != c, !(a == c)));

  ASSERT_TRUE(iff(b != a, !(b == a)));
  ASSERT_TRUE(iff(b != b, !(b == b)));
  ASSERT_TRUE(iff(b != c, !(b == c)));

  ASSERT_TRUE(iff(c != a, !(c == a)));
  ASSERT_TRUE(iff(c != b, !(c == b)));
  ASSERT_TRUE(iff(c != c, !(c == c)));

  ASSERT_TRUE(!(d != d));

  ASSERT_TRUE(d != a);
  ASSERT_TRUE(d != b);
  ASSERT_TRUE(d != c);
}

/* operator[] */
TEST_F(TestNodeBlackNode, operator_square)
{
#ifdef CVC4_ASSERTIONS
  // Basic bounds check on a node w/out children
  ASSERT_DEATH(Node::null()[-1], "i >= 0 && unsigned\\(i\\) < d_nchildren");
  ASSERT_DEATH(Node::null()[0], "i >= 0 && unsigned\\(i\\) < d_nchildren");
#endif

  // Basic access check
  Node tb = d_nodeManager->mkConst(true);
  Node eb = d_nodeManager->mkConst(false);
  Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  Node ite = cnd.iteNode(tb, eb);

  ASSERT_EQ(tb, cnd[0]);
  ASSERT_EQ(eb, cnd[1]);

  ASSERT_EQ(cnd, ite[0]);
  ASSERT_EQ(tb, ite[1]);
  ASSERT_EQ(eb, ite[2]);

#ifdef CVC4_ASSERTIONS
  // Bounds check on a node with children
  ASSERT_DEATH(ite == ite[-1], "i >= 0 && unsigned\\(i\\) < d_nchildren");
  ASSERT_DEATH(ite == ite[4], "i >= 0 && unsigned\\(i\\) < d_nchildren");
#endif
}

/* operator= */
TEST_F(TestNodeBlackNode, operator_assign)
{
  Node a, b;
  Node c = d_nodeManager->mkNode(
      NOT, d_nodeManager->mkSkolem("c", d_nodeManager->booleanType()));

  b = c;
  ASSERT_EQ(b, c);

  a = b = c;

  ASSERT_EQ(a, b);
  ASSERT_EQ(a, c);
}

/* operator< */
TEST_F(TestNodeBlackNode, operator_less_than)
{
  // We don't have access to the ids so we can't test the implementation
  // in the black box tests.

  Node a = d_nodeManager->mkSkolem("a", d_nodeManager->booleanType());
  Node b = d_nodeManager->mkSkolem("b", d_nodeManager->booleanType());

  ASSERT_TRUE(a < b || b < a);
  ASSERT_TRUE(!(a < b && b < a));

  Node c = d_nodeManager->mkNode(AND, a, b);
  Node d = d_nodeManager->mkNode(AND, a, b);

  ASSERT_FALSE(c < d);
  ASSERT_FALSE(d < c);

  // simple test of descending descendant property
  Node child = d_nodeManager->mkConst(true);
  Node parent = d_nodeManager->mkNode(NOT, child);

  ASSERT_TRUE(child < parent);

  // slightly less simple test of DD property
  std::vector<Node> chain;
  const int N = 500;
  Node curr = d_nodeManager->mkNode(OR, a, b);
  chain.push_back(curr);
  for (int i = 0; i < N; ++i)
  {
    curr = d_nodeManager->mkNode(AND, curr, curr);
    chain.push_back(curr);
  }

  for (int i = 0; i < N; ++i)
  {
    for (int j = i + 1; j < N; ++j)
    {
      Node chain_i = chain[i];
      Node chain_j = chain[j];
      ASSERT_TRUE(chain_i < chain_j);
    }
  }
}

TEST_F(TestNodeBlackNode, eqNode)
{
  TypeNode t = d_nodeManager->mkSort();
  Node left = d_nodeManager->mkSkolem("left", t);
  Node right = d_nodeManager->mkSkolem("right", t);
  Node eq = left.eqNode(right);

  ASSERT_EQ(EQUAL, eq.getKind());
  ASSERT_EQ(2, eq.getNumChildren());

  ASSERT_EQ(eq[0], left);
  ASSERT_EQ(eq[1], right);
}

TEST_F(TestNodeBlackNode, notNode)
{
  Node child = d_nodeManager->mkConst(true);
  Node parent = child.notNode();

  ASSERT_EQ(NOT, parent.getKind());
  ASSERT_EQ(1, parent.getNumChildren());

  ASSERT_EQ(parent[0], child);
}

TEST_F(TestNodeBlackNode, andNode)
{
  Node left = d_nodeManager->mkConst(true);
  Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
  Node eq = left.andNode(right);

  ASSERT_EQ(AND, eq.getKind());
  ASSERT_EQ(2, eq.getNumChildren());

  ASSERT_EQ(*(eq.begin()), left);
  ASSERT_EQ(*(++eq.begin()), right);
}

TEST_F(TestNodeBlackNode, orNode)
{
  Node left = d_nodeManager->mkConst(true);
  Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
  Node eq = left.orNode(right);

  ASSERT_EQ(OR, eq.getKind());
  ASSERT_EQ(2, eq.getNumChildren());

  ASSERT_EQ(*(eq.begin()), left);
  ASSERT_EQ(*(++eq.begin()), right);
}

TEST_F(TestNodeBlackNode, iteNode)
{
  Node a = d_nodeManager->mkSkolem("a", d_nodeManager->booleanType());
  Node b = d_nodeManager->mkSkolem("b", d_nodeManager->booleanType());

  Node cnd = d_nodeManager->mkNode(OR, a, b);
  Node thenBranch = d_nodeManager->mkConst(true);
  Node elseBranch = d_nodeManager->mkNode(NOT, d_nodeManager->mkConst(false));
  Node ite = cnd.iteNode(thenBranch, elseBranch);

  ASSERT_EQ(ITE, ite.getKind());
  ASSERT_EQ(3, ite.getNumChildren());

  ASSERT_EQ(*(ite.begin()), cnd);
  ASSERT_EQ(*(++ite.begin()), thenBranch);
  ASSERT_EQ(*(++(++ite.begin())), elseBranch);
}

TEST_F(TestNodeBlackNode, iffNode)
{
  Node left = d_nodeManager->mkConst(true);
  Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
  Node eq = left.eqNode(right);

  ASSERT_EQ(EQUAL, eq.getKind());
  ASSERT_EQ(2, eq.getNumChildren());

  ASSERT_EQ(*(eq.begin()), left);
  ASSERT_EQ(*(++eq.begin()), right);
}

TEST_F(TestNodeBlackNode, impNode)
{
  Node left = d_nodeManager->mkConst(true);
  Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
  Node eq = left.impNode(right);

  ASSERT_EQ(IMPLIES, eq.getKind());
  ASSERT_EQ(2, eq.getNumChildren());

  ASSERT_EQ(*(eq.begin()), left);
  ASSERT_EQ(*(++eq.begin()), right);
}

TEST_F(TestNodeBlackNode, xorNode)
{
  Node left = d_nodeManager->mkConst(true);
  Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
  Node eq = left.xorNode(right);

  ASSERT_EQ(XOR, eq.getKind());
  ASSERT_EQ(2, eq.getNumChildren());

  ASSERT_EQ(*(eq.begin()), left);
  ASSERT_EQ(*(++eq.begin()), right);
}

TEST_F(TestNodeBlackNode, getKind)
{
  Node a = d_nodeManager->mkSkolem("a", d_nodeManager->booleanType());
  Node b = d_nodeManager->mkSkolem("b", d_nodeManager->booleanType());

  Node n = d_nodeManager->mkNode(NOT, a);
  ASSERT_EQ(NOT, n.getKind());

  n = d_nodeManager->mkNode(EQUAL, a, b);
  ASSERT_EQ(EQUAL, n.getKind());

  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->realType());
  Node y = d_nodeManager->mkSkolem("y", d_nodeManager->realType());

  n = d_nodeManager->mkNode(PLUS, x, y);
  ASSERT_EQ(PLUS, n.getKind());

  n = d_nodeManager->mkNode(UMINUS, x);
  ASSERT_EQ(UMINUS, n.getKind());
}

TEST_F(TestNodeBlackNode, getOperator)
{
  TypeNode sort = d_nodeManager->mkSort("T");
  TypeNode booleanType = d_nodeManager->booleanType();
  TypeNode predType = d_nodeManager->mkFunctionType(sort, booleanType);

  Node f = d_nodeManager->mkSkolem("f", predType);
  Node a = d_nodeManager->mkSkolem("a", sort);
  Node fa = d_nodeManager->mkNode(kind::APPLY_UF, f, a);

  ASSERT_TRUE(fa.hasOperator());
  ASSERT_FALSE(f.hasOperator());
  ASSERT_FALSE(a.hasOperator());

  ASSERT_EQ(fa.getNumChildren(), 1);
  ASSERT_EQ(f.getNumChildren(), 0);
  ASSERT_EQ(a.getNumChildren(), 0);

  ASSERT_EQ(f, fa.getOperator());
#ifdef CVC4_ASSERTIONS
  ASSERT_THROW(f.getOperator(), IllegalArgumentException);
  ASSERT_THROW(a.getOperator(), IllegalArgumentException);
#endif
}

TEST_F(TestNodeBlackNode, getNumChildren)
{
  Node trueNode = d_nodeManager->mkConst(true);

  ASSERT_EQ(0, (Node::null()).getNumChildren());
  ASSERT_EQ(1, trueNode.notNode().getNumChildren());
  ASSERT_EQ(2, trueNode.andNode(trueNode).getNumChildren());

  srand(0);
  for (uint32_t i = 0; i < 500; ++i)
  {
    uint32_t n = rand() % 1000 + 2;
    testNaryExpForSize(AND, n);
  }

#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(testNaryExpForSize(AND, 0),
               "getNumChildren\\(\\) >= "
               "kind::metakind::getLowerBoundForKind\\(getKind\\(\\)\\)");
  ASSERT_DEATH(testNaryExpForSize(AND, 1),
               "getNumChildren\\(\\) >= "
               "kind::metakind::getLowerBoundForKind\\(getKind\\(\\)\\)");
  ASSERT_DEATH(testNaryExpForSize(NOT, 0),
               "getNumChildren\\(\\) >= "
               "kind::metakind::getLowerBoundForKind\\(getKind\\(\\)\\)");
  ASSERT_DEATH(testNaryExpForSize(NOT, 2),
               "getNumChildren\\(\\) <= "
               "kind::metakind::getUpperBoundForKind\\(getKind\\(\\)\\)");
#endif /* CVC4_ASSERTIONS */
}

TEST_F(TestNodeBlackNode, iterator)
{
  NodeBuilder<> b;
  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->booleanType());
  Node y = d_nodeManager->mkSkolem("y", d_nodeManager->booleanType());
  Node z = d_nodeManager->mkSkolem("z", d_nodeManager->booleanType());
  Node n = b << x << y << z << kind::AND;

  {  // iterator
    Node::iterator i = n.begin();
    ASSERT_EQ(*i++, x);
    ASSERT_EQ(*i++, y);
    ASSERT_EQ(*i++, z);
    ASSERT_EQ(i, n.end());
  }

  {  // same for const iterator
    const Node& c = n;
    Node::const_iterator i = c.begin();
    ASSERT_EQ(*i++, x);
    ASSERT_EQ(*i++, y);
    ASSERT_EQ(*i++, z);
    ASSERT_EQ(i, n.end());
  }
}

TEST_F(TestNodeBlackNode, kinded_iterator)
{
  TypeNode integerType = d_nodeManager->integerType();

  Node x = d_nodeManager->mkSkolem("x", integerType);
  Node y = d_nodeManager->mkSkolem("y", integerType);
  Node z = d_nodeManager->mkSkolem("z", integerType);
  Node plus_x_y_z = d_nodeManager->mkNode(kind::PLUS, x, y, z);
  Node x_minus_y = d_nodeManager->mkNode(kind::MINUS, x, y);

  {  // iterator
    Node::kinded_iterator i = plus_x_y_z.begin(PLUS);
    ASSERT_EQ(*i++, x);
    ASSERT_EQ(*i++, y);
    ASSERT_EQ(*i++, z);
    ASSERT_TRUE(i == plus_x_y_z.end(PLUS));

    i = x.begin(PLUS);
    ASSERT_EQ(*i++, x);
    ASSERT_TRUE(i == x.end(PLUS));
  }
}

TEST_F(TestNodeBlackNode, toString)
{
  TypeNode booleanType = d_nodeManager->booleanType();

  Node w = d_nodeManager->mkSkolem(
      "w", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node x = d_nodeManager->mkSkolem(
      "x", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node y = d_nodeManager->mkSkolem(
      "y", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node z = d_nodeManager->mkSkolem(
      "z", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node m = NodeBuilder<>() << w << x << kind::OR;
  Node n = NodeBuilder<>() << m << y << z << kind::AND;

  ASSERT_EQ(n.toString(), "(AND (OR w x) y z)");
}

TEST_F(TestNodeBlackNode, toStream)
{
  TypeNode booleanType = d_nodeManager->booleanType();

  Node w = d_nodeManager->mkSkolem(
      "w", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node x = d_nodeManager->mkSkolem(
      "x", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node y = d_nodeManager->mkSkolem(
      "y", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node z = d_nodeManager->mkSkolem(
      "z", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node m = NodeBuilder<>() << x << y << kind::OR;
  Node n = NodeBuilder<>() << w << m << z << kind::AND;
  Node o = NodeBuilder<>() << n << n << kind::XOR;

  std::stringstream sstr;
  sstr << Node::dag(false);
  n.toStream(sstr);
  ASSERT_EQ(sstr.str(), "(AND w (OR x y) z)");

  sstr.str(std::string());
  o.toStream(sstr, -1, 0);
  ASSERT_EQ(sstr.str(), "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");

  sstr.str(std::string());
  sstr << n;
  ASSERT_EQ(sstr.str(), "(AND w (OR x y) z)");

  sstr.str(std::string());
  sstr << o;
  ASSERT_EQ(sstr.str(), "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");

  sstr.str(std::string());
  sstr << Node::setdepth(0) << n;
  ASSERT_EQ(sstr.str(), "(AND w (OR x y) z)");

  sstr.str(std::string());
  sstr << Node::setdepth(0) << o;
  ASSERT_EQ(sstr.str(), "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");

  sstr.str(std::string());
  sstr << Node::setdepth(1) << n;
  ASSERT_EQ(sstr.str(), "(AND w (OR (...) (...)) z)");

  sstr.str(std::string());
  sstr << Node::setdepth(1) << o;
  ASSERT_EQ(sstr.str(),
            "(XOR (AND (...) (...) (...)) (AND (...) (...) (...)))");

  sstr.str(std::string());
  sstr << Node::setdepth(2) << n;
  ASSERT_EQ(sstr.str(), "(AND w (OR x y) z)");

  sstr.str(std::string());
  sstr << Node::setdepth(2) << o;
  ASSERT_EQ(sstr.str(),
            "(XOR (AND w (OR (...) (...)) z) (AND w (OR (...) (...)) z))");

  sstr.str(std::string());
  sstr << Node::setdepth(3) << n;
  ASSERT_EQ(sstr.str(), "(AND w (OR x y) z)");

  sstr.str(std::string());
  sstr << Node::setdepth(3) << o;
  ASSERT_EQ(sstr.str(), "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");
}

TEST_F(TestNodeBlackNode, dagifier)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode fnType = d_nodeManager->mkFunctionType(intType, intType);

  Node x =
      d_nodeManager->mkSkolem("x", intType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node y =
      d_nodeManager->mkSkolem("y", intType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node f =
      d_nodeManager->mkSkolem("f", fnType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node g =
      d_nodeManager->mkSkolem("g", fnType, "", NodeManager::SKOLEM_EXACT_NAME);
  Node fx = d_nodeManager->mkNode(APPLY_UF, f, x);
  Node fy = d_nodeManager->mkNode(APPLY_UF, f, y);
  Node gx = d_nodeManager->mkNode(APPLY_UF, g, x);
  Node gy = d_nodeManager->mkNode(APPLY_UF, g, y);
  Node fgx = d_nodeManager->mkNode(APPLY_UF, f, gx);
  Node ffx = d_nodeManager->mkNode(APPLY_UF, f, fx);
  Node fffx = d_nodeManager->mkNode(APPLY_UF, f, ffx);
  Node fffx_eq_x = d_nodeManager->mkNode(EQUAL, fffx, x);
  Node fffx_eq_y = d_nodeManager->mkNode(EQUAL, fffx, y);
  Node fx_eq_gx = d_nodeManager->mkNode(EQUAL, fx, gx);
  Node x_eq_y = d_nodeManager->mkNode(EQUAL, x, y);
  Node fgx_eq_gy = d_nodeManager->mkNode(EQUAL, fgx, gy);

  Node n = d_nodeManager->mkNode(
      OR, fffx_eq_x, fffx_eq_y, fx_eq_gx, x_eq_y, fgx_eq_gy);

  std::stringstream sstr;
  sstr << Node::setdepth(-1) << Node::setlanguage(language::output::LANG_CVC4);
  sstr << Node::dag(false) << n;  // never dagify
  ASSERT_EQ(sstr.str(),
            "(f(f(f(x))) = x) OR (f(f(f(x))) = y) OR (f(x) = g(x)) OR (x = "
            "y) OR (f(g(x)) = g(y))");
}

TEST_F(TestNodeBlackNode, for_each_over_nodes_as_node)
{
  const std::vector<Node> skolems =
      makeNSkolemNodes(d_nodeManager.get(), 3, d_nodeManager->integerType());
  Node add = d_nodeManager->mkNode(kind::PLUS, skolems);
  std::vector<Node> children;
  for (Node child : add)
  {
    children.push_back(child);
  }
  ASSERT_TRUE(children.size() == skolems.size()
              && std::equal(children.begin(), children.end(), skolems.begin()));
}

TEST_F(TestNodeBlackNode, for_each_over_nodes_as_tnode)
{
  const std::vector<Node> skolems =
      makeNSkolemNodes(d_nodeManager.get(), 3, d_nodeManager->integerType());
  Node add = d_nodeManager->mkNode(kind::PLUS, skolems);
  std::vector<TNode> children;
  for (TNode child : add)
  {
    children.push_back(child);
  }
  ASSERT_TRUE(children.size() == skolems.size()
              && std::equal(children.begin(), children.end(), skolems.begin()));
}

TEST_F(TestNodeBlackNode, for_each_over_tnodes_as_node)
{
  const std::vector<Node> skolems =
      makeNSkolemNodes(d_nodeManager.get(), 3, d_nodeManager->integerType());
  Node add_node = d_nodeManager->mkNode(kind::PLUS, skolems);
  TNode add_tnode = add_node;
  std::vector<Node> children;
  for (Node child : add_tnode)
  {
    children.push_back(child);
  }
  ASSERT_TRUE(children.size() == skolems.size()
              && std::equal(children.begin(), children.end(), skolems.begin()));
}

TEST_F(TestNodeBlackNode, for_each_over_tnodes_as_tnode)
{
  const std::vector<Node> skolems =
      makeNSkolemNodes(d_nodeManager.get(), 3, d_nodeManager->integerType());
  Node add_node = d_nodeManager->mkNode(kind::PLUS, skolems);
  TNode add_tnode = add_node;
  std::vector<TNode> children;
  for (TNode child : add_tnode)
  {
    children.push_back(child);
  }
  ASSERT_TRUE(children.size() == skolems.size()
              && std::equal(children.begin(), children.end(), skolems.begin()));
}

TEST_F(TestNodeBlackNode, isConst)
{
  // more complicated "constants" exist in datatypes and arrays theories
  DType list("list");
  std::shared_ptr<DTypeConstructor> consC =
      std::make_shared<DTypeConstructor>("cons");
  consC->addArg("car", d_nodeManager->integerType());
  consC->addArgSelf("cdr");
  list.addConstructor(consC);
  list.addConstructor(std::make_shared<DTypeConstructor>("nil"));
  TypeNode listType = d_nodeManager->mkDatatypeType(list);
  const std::vector<std::shared_ptr<DTypeConstructor> >& lcons =
      listType.getDType().getConstructors();
  Node cons = lcons[0]->getConstructor();
  Node nil = lcons[1]->getConstructor();
  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->integerType());
  Node cons_x_nil =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR,
                            cons,
                            x,
                            d_nodeManager->mkNode(APPLY_CONSTRUCTOR, nil));
  Node cons_1_nil =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR,
                            cons,
                            d_nodeManager->mkConst(Rational(1)),
                            d_nodeManager->mkNode(APPLY_CONSTRUCTOR, nil));
  Node cons_1_cons_2_nil = d_nodeManager->mkNode(
      APPLY_CONSTRUCTOR,
      cons,
      d_nodeManager->mkConst(Rational(1)),
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR,
                            cons,
                            d_nodeManager->mkConst(Rational(2)),
                            d_nodeManager->mkNode(APPLY_CONSTRUCTOR, nil)));
  ASSERT_TRUE(d_nodeManager->mkNode(APPLY_CONSTRUCTOR, nil).isConst());
  ASSERT_FALSE(cons_x_nil.isConst());
  ASSERT_TRUE(cons_1_nil.isConst());
  ASSERT_TRUE(cons_1_cons_2_nil.isConst());

  TypeNode arrType = d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                                d_nodeManager->integerType());
  Node zero = d_nodeManager->mkConst(Rational(0));
  Node one = d_nodeManager->mkConst(Rational(1));
  Node storeAll = d_nodeManager->mkConst(ArrayStoreAll(arrType, zero));
  ASSERT_TRUE(storeAll.isConst());

  Node arr = d_nodeManager->mkNode(STORE, storeAll, zero, zero);
  ASSERT_FALSE(arr.isConst());
  arr = d_nodeManager->mkNode(STORE, storeAll, zero, one);
  ASSERT_TRUE(arr.isConst());
  Node arr2 = d_nodeManager->mkNode(STORE, arr, one, zero);
  ASSERT_FALSE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, zero, one);
  ASSERT_FALSE(arr2.isConst());

  arrType = d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(1),
                                       d_nodeManager->mkBitVectorType(1));
  zero = d_nodeManager->mkConst(BitVector(1, unsigned(0)));
  one = d_nodeManager->mkConst(BitVector(1, unsigned(1)));
  storeAll = d_nodeManager->mkConst(ArrayStoreAll(arrType, zero));
  ASSERT_TRUE(storeAll.isConst());

  arr = d_nodeManager->mkNode(STORE, storeAll, zero, zero);
  ASSERT_FALSE(arr.isConst());
  arr = d_nodeManager->mkNode(STORE, storeAll, zero, one);
  ASSERT_TRUE(arr.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, zero);
  ASSERT_FALSE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, one);
  ASSERT_FALSE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, zero, one);
  ASSERT_FALSE(arr2.isConst());
}

namespace {
Node level0(NodeManager* nm)
{
  NodeBuilder<> nb(kind::AND);
  Node x = nm->mkSkolem("x", nm->booleanType());
  nb << x;
  nb << x;
  return Node(nb.constructNode());
}
TNode level1(NodeManager* nm) { return level0(nm); }
}  // namespace

/**
 * This is for demonstrating what a certain type of user error looks like.
 */
TEST_F(TestNodeBlackNode, node_tnode_usage)
{
  Node n;
  ASSERT_NO_FATAL_FAILURE(n = level0(d_nodeManager.get()));
  ASSERT_DEATH(n = level1(d_nodeManager.get()), "d_nv->d_rc > 0");
}

}  // namespace test
}  // namespace CVC4
