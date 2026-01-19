/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for arithmetic polynomial normalization.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/env.h"
#include "test_smt.h"
#include "theory/arith/liastar/liastar_extension.h"
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
  Node zero, one, two, three, nine, twentyOne;
  NodeManager* nm;
  Env* e;
  std::stringstream ss;
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
    three = nm->mkConstInt(Rational(3));
    nine = nm->mkConstInt(Rational(9));
    twentyOne = nm->mkConstInt(Rational(21));
  }
};

TEST_F(TestLiaStarUtils, toDNF)
{
  // (not (>= (+ (* 3 x) (* (- 1) y)) 9)), i.e., not (3*x - y >= 9)
  // expected (9 >= 3 * x - y + 1)
  // (>= 9 (+ (- (* 3 x) y) 1))

  Node x = nm->mkBoundVar("x", intType);
  Node y = nm->mkBoundVar("y", intType);
  Node threeTimesX = nm->mkNode(Kind::MULT, three, x);
  Node minus = nm->mkNode(Kind::SUB, threeTimesX, y);
  Node geq = nm->mkNode(Kind::GEQ, minus, nine);
  Node notGEQ = geq.notNode();
  Node dnf = LiaStarUtils::toDNF(notGEQ, e);
  Node expected =
      nm->mkNode(Kind::GEQ, nine, nm->mkNode(Kind::ADD, minus, one));
  ASSERT_EQ(expected, dnf);

  // 2x + 3y <= 20
  // (not (>= (+ (* 2 x) (* 3 y)) 21)), i.e., 2x + 3y <= 20
  // expected (21 >= (+ (+ (* 2 x) (* 3 y)) 1))
  // (>= 21 (+ (+ (* 2 x) (* 3 y)) 1))

  Node twoTimesX = nm->mkNode(Kind::MULT, two, x);
  Node threeTimesY = nm->mkNode(Kind::MULT, three, y);
  Node plus = nm->mkNode(Kind::ADD, twoTimesX, threeTimesY);
  geq = nm->mkNode(Kind::GEQ, plus, twentyOne);
  notGEQ = geq.notNode();
  dnf = LiaStarUtils::toDNF(notGEQ, e);
  expected = nm->mkNode(
      Kind::GEQ, twentyOne, nm->mkNode(Kind::ADD, twoTimesX, threeTimesY, one));
  ASSERT_EQ(expected, dnf);
}

TEST_F(TestLiaStarUtils, toDNF2008Paper)
{
  // F*(x1, L, x, z1, z2)
  // z1 = ite(x1 = ite(L <= x, 0, L − x), 0, 1) ∧  z2 = ite(x <= L, 0, 1) or
  // (and
  //  (= z1 (ite (= x1 (ite (<= L x) 0 (- L x))) 0 1))
  //  (= z2 (ite (<= x L) 0 1)))
  Node x1 = nm->mkBoundVar("x1", intType);
  Node L = nm->mkBoundVar("L", intType);
  Node x = nm->mkBoundVar("x", intType);
  Node z1 = nm->mkBoundVar("z1", intType);
  Node z2 = nm->mkBoundVar("z2", intType);
  Node L_leq_x = nm->mkNode(Kind::LEQ, L, x);
  Node L_minus_x = nm->mkNode(Kind::SUB, L, x);
  Node x1_ite = nm->mkNode(Kind::ITE, L_leq_x, zero, L_minus_x);
  Node x1_eq = x1.eqNode(x1_ite);
  Node z1_ite = nm->mkNode(Kind::ITE, x1_eq, zero, one);
  Node z1_eq = z1.eqNode(z1_ite);
  Node x_leq_L = nm->mkNode(Kind::LEQ, x, L);
  Node z2_ite = nm->mkNode(Kind::ITE, x_leq_L, zero, one);
  Node z2_eq = z2.eqNode(z2_ite);

  Node F = z1_eq.andNode(z2_eq);
  std::cout << "F: " << F.toString() << std::endl;
  Node dnf = LiaStarUtils::toDNF(F, e);
  std::cout << "dnf: " << dnf.toString() << std::endl;
  ASSERT_EQ(one, F);
  ASSERT_EQ(one, dnf);
}

}  // namespace test
}  // namespace cvc5::internal