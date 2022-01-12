/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Abdalrhman Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"

namespace cvc5 {

using namespace theory;
using namespace theory::bv;
using namespace theory::bv::utils;
using namespace expr;
using namespace context;

namespace test {

class TestTheoryWhiteBv : public TestSmtNoFinishInit
{
};

TEST_F(TestTheoryWhiteBv, mkUmulo)
{
  d_slvEngine->setOption("incremental", "true");
  for (uint32_t w = 1; w < 16; ++w)
  {
    d_slvEngine->push();
    Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(w));
    Node y = d_nodeManager->mkVar("y", d_nodeManager->mkBitVectorType(w));

    Node zx = mkConcat(mkZero(w), x);
    Node zy = mkConcat(mkZero(w), y);
    Node mul = d_nodeManager->mkNode(kind::BITVECTOR_MULT, zx, zy);
    Node lhs = d_nodeManager->mkNode(
        kind::DISTINCT, mkExtract(mul, 2 * w - 1, w), mkZero(w));
    Node rhs = mkUmulo(x, y);
    Node eq = d_nodeManager->mkNode(kind::DISTINCT, lhs, rhs);
    d_slvEngine->assertFormula(eq);
    Result res = d_slvEngine->checkSat();
    ASSERT_EQ(res.isSat(), Result::UNSAT);
    d_slvEngine->pop();
  }
}
}  // namespace test
}  // namespace cvc5
