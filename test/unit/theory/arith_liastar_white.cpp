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

namespace test {

class TestLiaStarUtils : public TestSmt
{
 protected:
  void SetUp() override { TestSmt::SetUp(); }
};

TEST_F(TestLiaStarUtils, toDNF)
{
  // (not (>= (+ (* 3 x) (* (- 1) y)) 9))
  TypeNode intType = d_nodeManager->integerType();
  Node three = d_nodeManager->mkConstInt(Rational(3));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node nine = d_nodeManager->mkConstInt(Rational(9));
  Node x = d_nodeManager->mkBoundVar("x", intType);
  Node y = d_nodeManager->mkBoundVar("y", intType);
  Node threeTimesX = d_nodeManager->mkNode(Kind::MULT, three, x);
  Node minus = d_nodeManager->mkNode(Kind::SUB, threeTimesX, y);
  Node gte = d_nodeManager->mkNode(Kind::GEQ, minus, nine);
  Node notGTE = gte.notNode();
  std::cout << "not: " << notGTE << std::endl;
  Env e(d_nodeManager.get(), nullptr);
  auto rw = e.getRewriter();
  Node r = rw->rewrite(notGTE);
  std::cout << "r: " << r << std::endl;
  Node dnf = liastar::LiaStarUtils::toDNF(notGTE, &e);
  std::cout << "dnf: " << dnf << std::endl;
  ASSERT_EQ(notGTE, dnf);
}
}  // namespace test
}  // namespace cvc5::internal