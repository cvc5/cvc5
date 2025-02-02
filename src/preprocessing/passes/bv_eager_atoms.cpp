/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrap assertions in BITVECTOR_EAGER_ATOM nodes.
 *
 * This preprocessing pass wraps all assertions in BITVECTOR_EAGER_ATOM nodes
 * and allows to use eager bit-blasting in the BV solver.
 */

#include "preprocessing/passes/bv_eager_atoms.h"

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "proof/proof.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * A proof generator for turning formulas F into (BITVECTOR_EAGER_ATOM F).
 */
class BVEagerAtomProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  BVEagerAtomProofGenerator(Env& env) : EnvObj(env) {}
  virtual ~BVEagerAtomProofGenerator() {}
  /**
   * Proves (BITVECTOR_EAGER_ATOM F) from F via:
   *
   *     ---------------------------- BV_EAGER_ATOM
   *     (BITVECTOR_EAGER_ATOM F) = F
   *     ---------------------------- SYMM
   *     F = (BITVECTOR_EAGER_ATOM F)
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override
  {
    Assert(fact.getKind() == Kind::EQUAL
           && fact[1].getKind() == Kind::BITVECTOR_EAGER_ATOM
           && fact[1][0] == fact[0]);
    CDProof cdp(d_env);
    Node eq = fact[1].eqNode(fact[0]);
    cdp.addStep(eq, ProofRule::BV_EAGER_ATOM, {}, {fact[1]});
    return cdp.getProofFor(fact);
  }
  /** identify */
  std::string identify() const override { return "BVEagerAtomProofGenerator"; }
};

BvEagerAtoms::BvEagerAtoms(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-eager-atoms"),
      d_proof(options().smt.produceProofs ? new BVEagerAtomProofGenerator(d_env)
                                          : nullptr)
{
}

PreprocessingPassResult BvEagerAtoms::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    TNode atom = (*assertionsToPreprocess)[i];
    if (atom.isConst())
    {
      // don't bother making true/false into atoms
      continue;
    }
    Node eager_atom = nm->mkNode(Kind::BITVECTOR_EAGER_ATOM, atom);
    assertionsToPreprocess->replace(i, eager_atom, d_proof.get());
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
