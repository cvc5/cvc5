/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the bit-vector arithmetic abstraction refinement lemmas.
 *
 * Verifies that every refinement lemma scheme `l[x,s,t]` is a sound over-
 * approximation of its operator, i.e. that `(x <op> s = t) => l` is valid.
 */

#include <memory>

#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/abstract/abstraction_lemmas.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/result.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::bv;
using namespace theory::bv::abstract;

namespace test {

class TestTheoryWhiteBvAbstractionLemmas : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("incremental", "true");
    d_slvEngine->finishInit();
  }

  /** Check if Boolean node `pred` is T_BV-valid (i.e. ~pred is unsat). */
  void assertValid(TNode pred, Kind op, LemmaKind kind, uint32_t w)
  {
    Result res = d_slvEngine->checkSat(pred.notNode());
    ASSERT_EQ(res.getStatus(), Result::UNSAT)
        << "lemma is not valid: op=" << op << " kind=" << kind << " w=" << w
        << "\n  " << pred;
  }

  /**
   * Check all symbolic (non-value) lemmas for the given operator.
   * A purely symbolic lemma implements the 3-argument `instance(x, s, t)`
   * and returns a null Node for `instance(x, s, t, xval, sval, tval)`.
   */
  void checkSymbolicLemma(Kind op)
  {
    NodeManager* nm = d_nodeManager.get();
    LemmaRegistry reg(nm);
    for (uint32_t w : {4u, 8u, 16u})
    {
      Node x = nm->mkVar("x", nm->mkBitVectorType(w));
      Node s = nm->mkVar("s", nm->mkBitVectorType(w));
      // t is bound to the true operator semantics.
      Node t = nm->mkNode(op, x, s);
      for (const std::unique_ptr<AbstractionLemma>& lemma : reg.lemmas(op))
      {
        Node inst = lemma->instance(x, s, t);
        if (inst.isNull())
        {
          continue;
        }
        assertValid(inst, op, lemma->getKind(), w);
      }
    }
  }

  /**
   * Check all model-value-based (power-of-two) lemmas for the given operator.
   * A model-value-based lemma returns a null node for `instance(x, s, t)`
   * and implements the 6-argument `instance(x, s, t, xval, sval, tval)`.
   */
  void checkModelValueBasedLemma(Kind op)
  {
    NodeManager* nm = d_nodeManager.get();
    LemmaRegistry reg(nm);
    for (uint32_t w : {4u, 8u, 16u})
    {
      Node x = nm->mkVar("x", nm->mkBitVectorType(w));
      Node s = nm->mkVar("s", nm->mkBitVectorType(w));
      Node t = nm->mkNode(op, x, s);
      for (const std::unique_ptr<AbstractionLemma>& lemma : reg.lemmas(op))
      {
        // Exercise the lemma with every (negated) power-of-two operand value;
        // the builder selects the applicable ones (pow2 for *_POW2, negated
        // pow2 for MUL_NEG_POW2) and returns null otherwise.
        for (uint32_t i = 0; i < w; ++i)
        {
          Node pos = utils::mkConst(nm, w, static_cast<unsigned>(1u << i));
          Node neg = utils::mkConst(
              nm, w, static_cast<unsigned>((1u << w) - (1u << i)));
          for (const Node& val : {pos, neg})
          {
            // val_x and val_s both set to the candidate; the builder reads the
            // operand relevant to its operator and ignores the other.
            Node inst = lemma->instance(x, s, t, val, val, t);
            if (inst.isNull())
            {
              continue;
            }
            assertValid(inst, op, lemma->getKind(), w);
          }
        }
      }
    }
  }
};

TEST_F(TestTheoryWhiteBvAbstractionLemmas, mul_symbolic)
{
  checkSymbolicLemma(Kind::BITVECTOR_MULT);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, udiv_symbolic)
{
  checkSymbolicLemma(Kind::BITVECTOR_UDIV);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, urem_symbolic)
{
  checkSymbolicLemma(Kind::BITVECTOR_UREM);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, mul_value)
{
  checkModelValueBasedLemma(Kind::BITVECTOR_MULT);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, udiv_value)
{
  checkModelValueBasedLemma(Kind::BITVECTOR_UDIV);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, urem_value)
{
  checkModelValueBasedLemma(Kind::BITVECTOR_UREM);
}

}  // namespace test
}  // namespace cvc5::internal
