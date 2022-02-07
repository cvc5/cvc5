/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the bit-vector rewriter.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

namespace cvc5 {

using namespace kind;
using namespace theory;

namespace test {

class TestTheoryWhiteBvRewriter : public TestSmt
{
 protected:
  Node boolToBv(Node b)
  {
    return d_nodeManager->mkNode(ITE,
                                 b,
                                 d_nodeManager->mkConst(BitVector(1, 1u)),
                                 d_nodeManager->mkConst(BitVector(1, 0u)));
  }
};

TEST_F(TestTheoryWhiteBvRewriter, rewrite_to_fixpoint)
{
  TypeNode boolType = d_nodeManager->booleanType();
  TypeNode bvType = d_nodeManager->mkBitVectorType(1);

  Node zero = d_nodeManager->mkConst(BitVector(1, 0u));
  Node b1 = d_nodeManager->mkVar("b1", boolType);
  Node b2 = d_nodeManager->mkVar("b2", boolType);
  Node b3 = d_nodeManager->mkVar("b3", boolType);
  Node bv = d_nodeManager->mkVar("bv", bvType);

  Node n = d_nodeManager->mkNode(
      BITVECTOR_ITE,
      boolToBv(b1),
      d_nodeManager->mkNode(
          BITVECTOR_ITE,
          boolToBv(b2),
          d_nodeManager->mkNode(BITVECTOR_ITE, boolToBv(b3), zero, bv),
          bv),
      bv);
  Node nr = Rewriter::rewrite(n);
  ASSERT_EQ(nr, Rewriter::rewrite(nr));
}

TEST_F(TestTheoryWhiteBvRewriter, rewrite_concat_to_fixpoint)
{
  TypeNode boolType = d_nodeManager->booleanType();
  TypeNode bvType = d_nodeManager->mkBitVectorType(4);

  Node zero = d_nodeManager->mkConst(BitVector(1, 0u));
  Node x = d_nodeManager->mkVar("bv", bvType);
  Node y = d_nodeManager->mkVar("bv", bvType);
  Node z = d_nodeManager->mkVar("bv", bvType);

  Node n = d_nodeManager->mkNode(
      BITVECTOR_CONCAT,
      bv::utils::mkExtract(d_nodeManager->mkNode(BITVECTOR_CONCAT, x, y), 7, 0),
      z);
  Node nr = Rewriter::rewrite(n);
  ASSERT_EQ(nr, Rewriter::rewrite(nr));
}

TEST_F(TestTheoryWhiteBvRewriter, rewrite_bv_ite)
{
  TypeNode boolType = d_nodeManager->booleanType();
  TypeNode bvType = d_nodeManager->mkBitVectorType(1);

  Node zero = d_nodeManager->mkConst(BitVector(1, 0u));
  Node c1 = d_nodeManager->mkVar("c1", bvType);
  Node c2 = d_nodeManager->mkVar("c2", bvType);

  Node ite = d_nodeManager->mkNode(BITVECTOR_ITE, c2, zero, zero);
  Node n = d_nodeManager->mkNode(BITVECTOR_ITE, c1, ite, ite);
  Node nr = Rewriter::rewrite(n);
  ASSERT_EQ(nr, Rewriter::rewrite(nr));
}

TEST_F(TestTheoryWhiteBvRewriter, rewrite_bv_comp)
{
  TypeNode bvType = d_nodeManager->mkBitVectorType(1);
  Node zero = d_nodeManager->mkConst(BitVector(1, 0u));
  Node x = d_nodeManager->mkVar("x", bvType);
  Node lhs = d_nodeManager->mkNode(BITVECTOR_NOT, x);
  Node rhs = d_nodeManager->mkNode(BITVECTOR_AND, zero, zero);
  Node n = d_nodeManager->mkNode(BITVECTOR_COMP, lhs, rhs);
  Node nr = Rewriter::rewrite(n);
  // bvcomp(bvnot(x), bvand(0, 0)) ---> x
  ASSERT_EQ(nr, x);
}

}  // namespace test
}  // namespace cvc5
