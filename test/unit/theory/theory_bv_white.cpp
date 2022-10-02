/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include <cmath>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/bitvector.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::bv;
using namespace theory::bv::utils;
using namespace expr;
using namespace context;

namespace test {

class TestTheoryWhiteBv : public TestSmtNoFinishInit
{
};

TEST_F(TestTheoryWhiteBv, umulo)
{
  d_slvEngine->setOption("incremental", "true");
  for (uint32_t w = 1; w < 8; ++w)
  {
    d_slvEngine->push();
    Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(w));
    Node y = d_nodeManager->mkVar("y", d_nodeManager->mkBitVectorType(w));

    Node zx = mkConcat(mkZero(w), x);
    Node zy = mkConcat(mkZero(w), y);
    Node mul = d_nodeManager->mkNode(kind::BITVECTOR_MULT, zx, zy);
    Node lhs = d_nodeManager->mkNode(
        kind::DISTINCT, mkExtract(mul, 2 * w - 1, w), mkZero(w));
    Node rhs = d_nodeManager->mkNode(kind::BITVECTOR_UMULO, x, y);
    Node eq = d_nodeManager->mkNode(kind::DISTINCT, lhs, rhs);
    d_slvEngine->assertFormula(eq);
    Result res = d_slvEngine->checkSat();
    ASSERT_EQ(res.getStatus(), Result::UNSAT);
    d_slvEngine->pop();
  }
}

TEST_F(TestTheoryWhiteBv, smulo)
{
  d_slvEngine->setOption("incremental", "true");
  for (uint32_t w = 1; w < 8; ++w)
  {
    d_slvEngine->push();
    Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(w));
    Node y = d_nodeManager->mkVar("y", d_nodeManager->mkBitVectorType(w));

    Node zx = mkSignExtend(x, w);
    Node zy = mkSignExtend(y, w);
    Node mul = d_nodeManager->mkNode(kind::BITVECTOR_MULT, zx, zy);

    Node max = d_nodeManager->mkConst(
        BitVector(2 * w, static_cast<uint32_t>(std::pow(2, w - 1))));
    Node min = d_nodeManager->mkNode(kind::BITVECTOR_NEG, max);

    Node lhs = d_nodeManager->mkNode(
        kind::OR,
        d_nodeManager->mkNode(kind::BITVECTOR_SLT, mul, min),
        d_nodeManager->mkNode(kind::BITVECTOR_SGE, mul, max));
    Node rhs = d_nodeManager->mkNode(kind::BITVECTOR_SMULO, x, y);
    Node eq = d_nodeManager->mkNode(kind::DISTINCT, lhs, rhs);
    d_slvEngine->assertFormula(eq);
    Result res = d_slvEngine->checkSat();
    ASSERT_EQ(res.getStatus(), Result::UNSAT);
    d_slvEngine->pop();
  }
}
}  // namespace test
}  // namespace cvc5::internal
