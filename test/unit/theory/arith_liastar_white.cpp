/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for lia star utilities.
 */

#ifdef CVC5_USE_NORMALIZ

#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/env.h"
#include "test_smt.h"
#include "theory/arith/liastar/liastar_utils.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::arith;
using namespace theory::arith::liastar;

namespace test {

class TestLiaStarUtils : public TestSmt
{
 protected:
  TypeNode intType;
  Node zero, one, two, x, y;
  NodeManager* nm;
  Env* e;

  void SetUp() override
  {
    TestSmt::SetUp();
    d_slvEngine->setOption("dag-thresh", "0", true);
    nm = d_nodeManager.get();
    e = &d_slvEngine->getEnv();
    intType = nm->integerType();
    zero = nm->mkConstInt(Rational(0));
    one = nm->mkConstInt(Rational(1));
    two = nm->mkConstInt(Rational(2));
    x = nm->mkBoundVar("x", intType);
    y = nm->mkBoundVar("y", intType);
  }

  Node boundVarList(const std::vector<Node>& vars)
  {
    return nm->mkNode(Kind::BOUND_VAR_LIST, vars);
  }

  Node lambda(const std::vector<Node>& vars, Node body)
  {
    return nm->mkNode(Kind::LAMBDA, boundVarList(vars), body);
  }
};

TEST_F(TestLiaStarUtils, getVectorPredicateInstantiatesLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  Node v = nm->mkBoundVar("v", intType);
  // (int.star-contains (lambda ((u Int) (v Int)) (>= u v)) x y)
  Node star = nm->mkNode(
      Kind::STAR_CONTAINS, lambda({u, v}, nm->mkNode(Kind::GEQ, u, v)), x, y);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkNode(Kind::GEQ, x, y), predicate);
  ASSERT_EQ("(and (and true (>= x 0)) (>= y 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getVectorPredicateAcceptsConstantLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  // (int.star-contains (lambda ((u Int)) false) x), where the rewriter
  // normalizes the constant lambda to a function array constant
  Node constantLambda =
      e->getRewriter()->rewrite(lambda({u}, nm->mkConst<bool>(false)));
  Node star = nm->mkNode(Kind::STAR_CONTAINS, constantLambda, x);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkConst<bool>(false), predicate);
  ASSERT_EQ("(and true (>= x 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getMatricesConjunctionIsOneMatrix)
{
  // (and (>= x 1) (= y 0)) over the coordinates (x y)
  Node conjunction = nm->mkNode(Kind::AND,
                                nm->mkNode(Kind::GEQ, x, one),
                                nm->mkNode(Kind::EQUAL, y, zero));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), conjunction);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] >= 1;", "x[2] = 0;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, getMatricesDisjunctionIsOneMatrixPerDisjunct)
{
  // (or (>= x 1) (>= y 2))
  Node disjunction = nm->mkNode(
      Kind::OR, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::GEQ, y, two));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), disjunction);

  ASSERT_EQ(2, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] >= 1;"}), matrices[0].first);
  ASSERT_EQ(std::vector<std::string>({"x[2] >= 2;"}), matrices[1].first);
}

TEST_F(TestLiaStarUtils, getMatricesPrintsCoefficients)
{
  // (>= (+ (* 2 x) y) 1)
  Node sum = nm->mkNode(Kind::ADD, nm->mkNode(Kind::MULT, two, x), y);
  Node constraint = nm->mkNode(Kind::GEQ, sum, one);

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), constraint);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"2x[1] + x[2] >= 1;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, cvc5CheckSatUnsat)
{
  // exists x. x >= 1 and x <= 0
  Node assertion = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::LEQ, x, zero));

  Result result = LiaStarUtils::cvc5CheckSat({x}, assertion, e);

  ASSERT_EQ(Result::Status::UNSAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, cvc5CheckSatSat)
{
  // exists x. x >= 1
  Node assertion = nm->mkNode(Kind::GEQ, x, one);

  Result result = LiaStarUtils::cvc5CheckSat({x}, assertion, e);

  ASSERT_EQ(Result::Status::SAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, areAssertionsUnsatConjoinsAssertions)
{
  // x >= 1 and x <= 0 are unsat together, satisfiable apart
  Node lower = nm->mkNode(Kind::GEQ, x, one);
  Node upper = nm->mkNode(Kind::LEQ, x, zero);

  ASSERT_EQ(Result::Status::UNSAT,
            LiaStarUtils::areAssertionsUnsat({lower, upper}, e).getStatus());
  ASSERT_EQ(Result::Status::SAT,
            LiaStarUtils::areAssertionsUnsat({lower}, e).getStatus());
}

TEST_F(TestLiaStarUtils, areAssertionsUnsatIsNoneWhenSubsolverIsDisabled)
{
  d_slvEngine->setOption("arith-liastar-subsolver", "false", true);
  Node lower = nm->mkNode(Kind::GEQ, x, one);
  Node upper = nm->mkNode(Kind::LEQ, x, zero);

  Result result = LiaStarUtils::areAssertionsUnsat({lower, upper}, e);

  ASSERT_EQ(Result::Status::NONE, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatEmptyConeIsUnsat)
{
  // x >= 1 and x <= 0 describe an empty cone
  Node assertion = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::LEQ, x, zero));

  Result result =
      LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false);

  ASSERT_EQ(Result::Status::UNSAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatNonemptyConeIsNone)
{
  // x >= 1 describes a nonempty cone, which is reported as none rather
  // than sat
  Node assertion = nm->mkNode(Kind::GEQ, x, one);

  Result result =
      LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false);

  ASSERT_EQ(Result::Status::NONE, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatAssumeNonnegative)
{
  // x <= -1 is satisfiable over the integers, but not over the
  // nonnegative orthant
  Node assertion = nm->mkNode(Kind::LEQ, x, nm->mkConstInt(Rational(-1)));

  ASSERT_EQ(Result::Status::NONE,
            LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false)
                .getStatus());
  ASSERT_EQ(Result::Status::UNSAT,
            LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, true)
                .getStatus());
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */
