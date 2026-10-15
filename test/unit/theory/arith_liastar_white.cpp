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

  Node boolVar(const std::string& name)
  {
    return nm->mkBoundVar(name, nm->booleanType());
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

TEST_F(TestLiaStarUtils, distribute1)
{
  Node a = boolVar("a"), b = boolVar("b"), f = boolVar("f"), g = boolVar("g");
  Node u = boolVar("u"), v = boolVar("v"), p = boolVar("p"), q = boolVar("q");
  Node z = boolVar("z");
  // (and
  //   (or
  //     (and
  //        (or f g)
  //        (or p q))
  //      z)
  //     (or u v)
  //   (and a b)
  //  )

  Node or_fg = nm->mkNode(Kind::OR, {f, g});
  Node or_xy = nm->mkNode(Kind::OR, {p, q});
  Node or_uv = nm->mkNode(Kind::OR, {u, v});
  Node and_ab = nm->mkNode(Kind::AND, {a, b});
  Node and_or_fg_or_xy = nm->mkNode(Kind::AND, {or_fg, or_xy});
  Node and_z = nm->mkNode(Kind::AND, {and_or_fg_or_xy, z});
  Node or_uv_z = nm->mkNode(Kind::OR, {or_uv, and_z});
  Node and_outer = nm->mkNode(Kind::AND, {or_uv_z, and_ab});
  Node dnf = LiaStarUtils::distribute(and_outer, e);
  dnf = LiaStarUtils::recursiveFlatten(nm, dnf);
  ASSERT_EQ(
      "(or (and a b u) (and a b v) (and a b z f p) (and a b z g p) (and a b z "
      "f q) (and a b z g q))",
      dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF1)
{
  // (not (>= (+ (* 3 x) (* (- 1) y)) 9)), i.e., not (3*x - y >= 9)
  Node three = nm->mkConstInt(Rational(3));
  Node nine = nm->mkConstInt(Rational(9));

  Node threeTimesX = nm->mkNode(Kind::MULT, three, x);
  Node minus = nm->mkNode(Kind::SUB, threeTimesX, y);
  Node geq = nm->mkNode(Kind::GEQ, minus, nine);
  Node notGEQ = geq.notNode();
  Node dnf = LiaStarUtils::toDNF(notGEQ, e);
  ASSERT_EQ("(< (- (* 3 x) y) 9)", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF2)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  // (and (or a b) (or c d))
  Node or_a_b = a.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b c) (and a d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF3)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or (and a p) b) (or c d))
  Node and_a_x = a.andNode(p);
  Node or_a_b = and_a_x.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a p c) (and b c) (and a p d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF4)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or a (and b p)) (or c d))
  Node and_b_x = b.andNode(p);
  Node or_a_b = a.orNode(and_b_x);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b p c) (and a d) (and b p d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF5)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or a b p) (or c d))
  Node or1 = nm->mkNode(Kind::OR, {a, b, p});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node and = or1.andNode(or2);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b c) (and p c) (and a d) (and b d) (and p d))",
            dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF6)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p"), q = boolVar("q");
  // (and (or a b) (or c d) (or p q))
  Node or1 = nm->mkNode(Kind::OR, {a, b});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node or3 = nm->mkNode(Kind::OR, {p, q});
  Node and = nm->mkNode(Kind::AND, {or1, or2, or3});
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ(
      "(or (and a c p) (and b c p) (and a d p) (and b d p) (and a c q) (and b "
      "c q) (and a d q) (and b d q))",
      dnf.toString());
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */
