/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the CAD module for nonlinear arithmetic.
 */

#ifdef CVC5_USE_POLY

#include <poly/polyxx.h>

#include <iostream>
#include <memory>
#include <vector>

#include "test_smt.h"
#include "theory/arith/nl/cad/cdcac.h"
#include "theory/arith/nl/cad/lazard_evaluation.h"
#include "theory/arith/nl/cad/projections.h"
#include "theory/arith/nl/cad_solver.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/arith/theory_arith.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/poly_util.h"

namespace cvc5::test {

using namespace cvc5;
using namespace cvc5::theory;
using namespace cvc5::theory::arith;
using namespace cvc5::theory::arith::nl;

NodeManager* nodeManager;
class TestTheoryWhiteArithCAD : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    d_realType.reset(new TypeNode(d_nodeManager->realType()));
    d_intType.reset(new TypeNode(d_nodeManager->integerType()));
    Trace.on("cad-check");
    nodeManager = d_nodeManager.get();
  }

  Node dummy(int i) const { return d_nodeManager->mkConst(Rational(i)); }

  Theory::Effort d_level = Theory::EFFORT_FULL;
  std::unique_ptr<TypeNode> d_realType;
  std::unique_ptr<TypeNode> d_intType;
  const Rational d_zero = 0;
  const Rational d_one = 1;
};

poly::AlgebraicNumber get_ran(std::initializer_list<long> init,
                              int lower,
                              int upper)
{
  return poly::AlgebraicNumber(poly::UPolynomial(init),
                               poly::DyadicInterval(lower, upper));
}

Node operator==(const Node& a, const Node& b)
{
  return nodeManager->mkNode(Kind::EQUAL, a, b);
}
Node operator>=(const Node& a, const Node& b)
{
  return nodeManager->mkNode(Kind::GEQ, a, b);
}
Node operator+(const Node& a, const Node& b)
{
  return nodeManager->mkNode(Kind::PLUS, a, b);
}
Node operator*(const Node& a, const Node& b)
{
  return nodeManager->mkNode(Kind::NONLINEAR_MULT, a, b);
}
Node operator!(const Node& a) { return nodeManager->mkNode(Kind::NOT, a); }
Node make_real_variable(const std::string& s)
{
  return nodeManager->mkSkolem(
      s, nodeManager->realType(), "", NodeManager::SKOLEM_EXACT_NAME);
}
Node make_int_variable(const std::string& s)
{
  return nodeManager->mkSkolem(
      s, nodeManager->integerType(), "", NodeManager::SKOLEM_EXACT_NAME);
}

TEST_F(TestTheoryWhiteArithCAD, test_univariate_isolation)
{
  poly::UPolynomial poly({-2, 2, 3, -3, -1, 1});
  auto roots = poly::isolate_real_roots(poly);

  EXPECT_TRUE(roots.size() == 4);
  EXPECT_TRUE(roots[0] == get_ran({-2, 0, 1}, -2, -1));
  EXPECT_TRUE(roots[1] == poly::Integer(-1));
  EXPECT_TRUE(roots[2] == poly::Integer(1));
  EXPECT_TRUE(roots[3] == get_ran({-2, 0, 1}, 1, 2));
}

TEST_F(TestTheoryWhiteArithCAD, test_multivariate_isolation)
{
  poly::Variable x("x");
  poly::Variable y("y");
  poly::Variable z("z");

  poly::Assignment a;
  a.set(x, get_ran({-2, 0, 1}, 1, 2));
  a.set(y, get_ran({-2, 0, 0, 0, 1}, 1, 2));

  poly::Polynomial poly = (y * y + x) - z;

  auto roots = poly::isolate_real_roots(poly, a);

  EXPECT_TRUE(roots.size() == 1);
  EXPECT_TRUE(roots[0] == get_ran({-8, 0, 1}, 2, 3));
}

TEST_F(TestTheoryWhiteArithCAD, test_univariate_factorization)
{
  poly::UPolynomial poly({-24, 44, -18, -1, 1, -3, 1});

  auto factors = square_free_factors(poly);
  std::sort(factors.begin(), factors.end());
  EXPECT_EQ(factors[0], poly::UPolynomial({-1, 1}));
  EXPECT_EQ(factors[1], poly::UPolynomial({-24, -4, -2, -1, 1}));
}

TEST_F(TestTheoryWhiteArithCAD, test_projection)
{
  // Gereon's thesis, Ex 5.1
  poly::Variable x("x");
  poly::Variable y("y");

  poly::Polynomial p = (y + 1) * (y + 1) - x * x * x + 3 * x - 2;
  poly::Polynomial q = (x + 1) * y - 3;

  auto res = cad::projectionMcCallum({p, q});
  std::sort(res.begin(), res.end());
  EXPECT_EQ(res[0], x - 1);
  EXPECT_EQ(res[1], x + 1);
  EXPECT_EQ(res[2], x + 2);
  EXPECT_EQ(res[3], x * x * x - 3 * x + 1);
  EXPECT_EQ(res[4],
            x * x * x * x * x + 2 * x * x * x * x - 2 * x * x * x - 5 * x * x
                - 7 * x - 14);
}

poly::Polynomial up_to_poly(const poly::UPolynomial& p, poly::Variable var)
{
  poly::Polynomial res;
  poly::Polynomial mult = 1;
  for (const auto& coeff : coefficients(p))
  {
    if (!is_zero(coeff))
    {
      res += mult * coeff;
    }
    mult *= var;
  }
  return res;
}

TEST_F(TestTheoryWhiteArithCAD, lazard_simp)
{
  Node a = d_nodeManager->mkVar(*d_realType);
  Node c = d_nodeManager->mkVar(*d_realType);
  Node orig = d_nodeManager->mkAnd(std::vector<Node>{
      d_nodeManager->mkNode(Kind::EQUAL, a, d_nodeManager->mkConst(d_zero)),
      d_nodeManager->mkNode(
          Kind::EQUAL,
          d_nodeManager->mkNode(
              Kind::PLUS,
              d_nodeManager->mkNode(Kind::NONLINEAR_MULT, a, c),
              d_nodeManager->mkConst(d_one)),
          d_nodeManager->mkConst(d_zero))});

  {
    Node rewritten = Rewriter::rewrite(orig);
    EXPECT_NE(rewritten, d_nodeManager->mkConst(false));
  }
  {
    quantifiers::ExtendedRewriter extrew;
    Node rewritten = extrew.extendedRewrite(orig);
    EXPECT_EQ(rewritten, d_nodeManager->mkConst(false));
  }
}

#ifdef CVC5_USE_COCOA
TEST_F(TestTheoryWhiteArithCAD, lazard_eval)
{
  poly::Variable x("x");
  poly::Variable y("y");
  poly::Variable z("z");
  poly::Variable f("f");
  poly::AlgebraicNumber ax = get_ran({-2, 0, 1}, 1, 2);
  poly::AlgebraicNumber ay = get_ran({-2, 0, 0, 0, 1}, 1, 2);
  poly::AlgebraicNumber az = get_ran({-3, 0, 1}, 1, 2);

  cad::LazardEvaluation lazard;
  lazard.add(x, ax);
  lazard.add(y, ay);
  lazard.add(z, az);

  poly::Polynomial q = (x * x - 2) * (y * y * y * y - 2) * z * f;
  lazard.addFreeVariable(f);
  auto qred = lazard.reducePolynomial(q);
  EXPECT_EQ(qred, std::vector<poly::Polynomial>{f});
}
#endif

TEST_F(TestTheoryWhiteArithCAD, test_cdcac_1)
{
  cad::CDCAC cac(nullptr, nullptr, {});
  poly::Variable x = cac.getConstraints().varMapper()(make_real_variable("x"));
  poly::Variable y = cac.getConstraints().varMapper()(make_real_variable("y"));

  cac.getConstraints().addConstraint(
      4 * y - x * x + 4, poly::SignCondition::LT, dummy(1));
  cac.getConstraints().addConstraint(
      4 * y - 4 + (x - 1) * (x - 1), poly::SignCondition::GT, dummy(2));
  cac.getConstraints().addConstraint(
      4 * y - x - 2, poly::SignCondition::GT, dummy(3));

  cac.computeVariableOrdering();

  auto cover = cac.getUnsatCover();
  EXPECT_TRUE(cover.empty());
  std::cout << "SAT: " << cac.getModel() << std::endl;
}

TEST_F(TestTheoryWhiteArithCAD, test_cdcac_2)
{
  cad::CDCAC cac(nullptr, nullptr, {});
  poly::Variable x = cac.getConstraints().varMapper()(make_real_variable("x"));
  poly::Variable y = cac.getConstraints().varMapper()(make_real_variable("y"));

  cac.getConstraints().addConstraint(y - pow(-x - 3, 11) + pow(-x - 3, 10) + 1,
                                     poly::SignCondition::GT,
                                     dummy(1));
  cac.getConstraints().addConstraint(
      2 * y - x + 2, poly::SignCondition::LT, dummy(2));
  cac.getConstraints().addConstraint(
      2 * y - 1 + x * x, poly::SignCondition::GT, dummy(3));
  cac.getConstraints().addConstraint(
      3 * y + x + 2, poly::SignCondition::LT, dummy(4));
  cac.getConstraints().addConstraint(
      y * y * y - pow(x - 2, 11) + pow(x - 2, 10) + 1,
      poly::SignCondition::GT,
      dummy(5));

  cac.computeVariableOrdering();

  auto cover = cac.getUnsatCover();
  EXPECT_TRUE(!cover.empty());
  auto nodes = cad::collectConstraints(cover);
  std::vector<Node> ref{dummy(1), dummy(2), dummy(3), dummy(4), dummy(5)};
  EXPECT_EQ(nodes, ref);
}

TEST_F(TestTheoryWhiteArithCAD, test_cdcac_3)
{
  cad::CDCAC cac(nullptr, nullptr, {});
  poly::Variable x = cac.getConstraints().varMapper()(make_real_variable("x"));
  poly::Variable y = cac.getConstraints().varMapper()(make_real_variable("y"));
  poly::Variable z = cac.getConstraints().varMapper()(make_real_variable("z"));

  cac.getConstraints().addConstraint(
      x * x + y * y + z * z - 1, poly::SignCondition::LT, dummy(1));
  cac.getConstraints().addConstraint(
      4 * x * x + (2 * y - 3) * (2 * y - 3) + 4 * z * z - 4,
      poly::SignCondition::LT,
      dummy(2));

  cac.computeVariableOrdering();

  auto cover = cac.getUnsatCover();
  EXPECT_TRUE(cover.empty());
  std::cout << "SAT: " << cac.getModel() << std::endl;
}

TEST_F(TestTheoryWhiteArithCAD, test_cdcac_4)
{
  cad::CDCAC cac(nullptr, nullptr, {});
  poly::Variable x = cac.getConstraints().varMapper()(make_real_variable("x"));
  poly::Variable y = cac.getConstraints().varMapper()(make_real_variable("y"));
  poly::Variable z = cac.getConstraints().varMapper()(make_real_variable("z"));

  cac.getConstraints().addConstraint(
      -z * z + y * y + x * x - 25, poly::SignCondition::GT, dummy(1));
  cac.getConstraints().addConstraint(
      (y - x - 6) * z * z - 9 * y * y + x * x - 1,
      poly::SignCondition::GT,
      dummy(2));
  cac.getConstraints().addConstraint(
      y * y - 100, poly::SignCondition::LT, dummy(3));

  cac.computeVariableOrdering();

  auto cover = cac.getUnsatCover();
  EXPECT_TRUE(cover.empty());
  std::cout << "SAT: " << cac.getModel() << std::endl;
}

void test_delta(const std::vector<Node>& a)
{
  cad::CDCAC cac(nullptr, nullptr, {});
  cac.reset();
  for (const Node& n : a)
  {
    cac.getConstraints().addConstraint(n);
  }
  cac.computeVariableOrdering();

  // Do full theory check here

  auto covering = cac.getUnsatCover();
  if (covering.empty())
  {
    std::cout << "SAT: " << cac.getModel() << std::endl;
  }
  else
  {
    auto mis = cad::collectConstraints(covering);
    std::cout << "Collected MIS: " << mis << std::endl;
    Assert(!mis.empty()) << "Infeasible subset can not be empty";
    Node lem = NodeManager::currentNM()->mkAnd(mis).negate();
    Notice() << "UNSAT with MIS: " << lem << std::endl;
  }
}

TEST_F(TestTheoryWhiteArithCAD, test_delta_one)
{
  std::vector<Node> a;
  Node zero = d_nodeManager->mkConst(Rational(0));
  Node one = d_nodeManager->mkConst(Rational(1));
  Node mone = d_nodeManager->mkConst(Rational(-1));
  Node fifth = d_nodeManager->mkConst(Rational(1, 2));
  Node g = make_real_variable("g");
  Node l = make_real_variable("l");
  Node q = make_real_variable("q");
  Node s = make_real_variable("s");
  Node u = make_real_variable("u");

  a.emplace_back(l == mone);
  a.emplace_back(!(g * s == zero));
  a.emplace_back(q * s == zero);
  a.emplace_back(u == zero);
  a.emplace_back(q == (one + (fifth * g * s)));
  a.emplace_back(l == u + q * s + (fifth * g * s * s));

  test_delta(a);
}

TEST_F(TestTheoryWhiteArithCAD, test_delta_two)
{
  std::vector<Node> a;
  Node zero = d_nodeManager->mkConst(Rational(0));
  Node one = d_nodeManager->mkConst(Rational(1));
  Node mone = d_nodeManager->mkConst(Rational(-1));
  Node fifth = d_nodeManager->mkConst(Rational(1, 2));
  Node g = make_real_variable("g");
  Node l = make_real_variable("l");
  Node q = make_real_variable("q");
  Node s = make_real_variable("s");
  Node u = make_real_variable("u");

  a.emplace_back(l == mone);
  a.emplace_back(!(g * s == zero));
  a.emplace_back(u == zero);
  a.emplace_back(q * s == zero);
  a.emplace_back(q == (one + (fifth * g * s)));
  a.emplace_back(l == u + q * s + (fifth * g * s * s));

  test_delta(a);
}

TEST_F(TestTheoryWhiteArithCAD, test_ran_conversion)
{
  RealAlgebraicNumber ran(
      std::vector<Rational>({-2, 0, 1}), Rational(1, 3), Rational(7, 3));
  {
    Node x = make_real_variable("x");
    Node n = nl::ran_to_node(ran, x);
    RealAlgebraicNumber back = nl::node_to_ran(n, x);
    EXPECT_TRUE(ran == back);
  }
}
}  // namespace cvc5::test

#endif
