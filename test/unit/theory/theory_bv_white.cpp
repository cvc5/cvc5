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
#include "theory/bv/bitblast/eager_bitblaster.h"
#include "theory/bv/bv_solver_lazy.h"
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

TEST_F(TestTheoryWhiteBv, bitblaster_core)
{
  d_smtEngine->setLogic("QF_BV");

  d_smtEngine->setOption("bitblast", "eager");
  d_smtEngine->setOption("incremental", "false");
  // Notice that this unit test uses the theory engine of a created SMT
  // engine d_smtEngine. We must ensure that d_smtEngine is properly initialized
  // via the following call, which constructs its underlying theory engine.
  d_smtEngine->finishInit();
  TheoryBV* tbv = dynamic_cast<TheoryBV*>(
      d_smtEngine->getTheoryEngine()->d_theoryTable[THEORY_BV]);
  BVSolverLazy* bvsl = dynamic_cast<BVSolverLazy*>(tbv->d_internal.get());
  std::unique_ptr<EagerBitblaster> bb(
      new EagerBitblaster(bvsl, d_smtEngine->getContext()));

  Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(16));
  Node y = d_nodeManager->mkVar("y", d_nodeManager->mkBitVectorType(16));
  Node x_plus_y = d_nodeManager->mkNode(kind::BITVECTOR_ADD, x, y);
  Node one = d_nodeManager->mkConst<BitVector>(BitVector(16, 1u));
  Node x_shl_one = d_nodeManager->mkNode(kind::BITVECTOR_SHL, x, one);
  Node eq = d_nodeManager->mkNode(kind::EQUAL, x_plus_y, x_shl_one);
  Node not_x_eq_y = d_nodeManager->mkNode(
      kind::NOT, d_nodeManager->mkNode(kind::EQUAL, x, y));

  bb->bbFormula(eq);
  bb->bbFormula(not_x_eq_y);

  ASSERT_EQ(bb->solve(), false);
}

TEST_F(TestTheoryWhiteBv, mkUmulo)
{
  d_smtEngine->setOption("incremental", "true");
  for (uint32_t w = 1; w < 16; ++w)
  {
    d_smtEngine->push();
    Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(w));
    Node y = d_nodeManager->mkVar("y", d_nodeManager->mkBitVectorType(w));

    Node zx = mkConcat(mkZero(w), x);
    Node zy = mkConcat(mkZero(w), y);
    Node mul = d_nodeManager->mkNode(kind::BITVECTOR_MULT, zx, zy);
    Node lhs = d_nodeManager->mkNode(
        kind::DISTINCT, mkExtract(mul, 2 * w - 1, w), mkZero(w));
    Node rhs = mkUmulo(x, y);
    Node eq = d_nodeManager->mkNode(kind::DISTINCT, lhs, rhs);
    d_smtEngine->assertFormula(eq);
    Result res = d_smtEngine->checkSat();
    ASSERT_EQ(res.isSat(), Result::UNSAT);
    d_smtEngine->pop();
  }
}
}  // namespace test
}  // namespace cvc5
