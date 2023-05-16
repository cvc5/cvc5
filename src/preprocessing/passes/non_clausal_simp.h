/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Non-clausal simplification preprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__NON_CLAUSAL_SIMP_H
#define CVC5__PREPROCESSING__PASSES__NON_CLAUSAL_SIMP_H

#include "context/cdlist.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "proof/trust_node.h"

namespace cvc5::internal {

class LazyCDProof;
class ProofNodeManager;

namespace smt {
class PreprocessProofGenerator;
}
namespace theory {
class TrustSubstitutionMap;
}

namespace preprocessing {
namespace passes {

class NonClausalSimp : public PreprocessingPass
{
 public:
  NonClausalSimp(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    IntStat d_numConstantProps;
    Statistics(StatisticsRegistry& reg);
  };

  Statistics d_statistics;
  /**
   * Transform learned literal lit. We apply substitutions in subs once and then
   * apply constant propagations cp to fixed point. Return the rewritten
   * form of lit.
   *
   * If proofs are enabled, then we require that the learned literal preprocess
   * proof generator (d_llpg) has a proof of lit when this method is called,
   * and ensure that the return literal also has a proof in d_llpg.
   */
  Node processLearnedLit(Node lit,
                         theory::TrustSubstitutionMap* subs,
                         theory::TrustSubstitutionMap* cp);
  /**
   * Process rewritten learned literal. This is called when we have a
   * learned literal lit that is rewritten to litr based on the proof generator
   * contained in trn (if it exists). The trust node trn should be of kind
   * REWRITE and proving (= lit litr).
   *
   * This tracks the proof in the learned literal preprocess proof generator
   * d_llpg below and returns the rewritten learned literal.
   */
  Node processRewrittenLearnedLit(TrustNode trn);
  /** Is proof enabled? */
  bool isProofEnabled() const;
  /** the learned literal preprocess proof generator */
  std::unique_ptr<smt::PreprocessProofGenerator> d_llpg;
  /**
   * An lazy proof for learned literals that are reasserted into the assertions
   * pipeline by this class.
   */
  std::unique_ptr<LazyCDProof> d_llra;
  /**
   * A context-dependent list of trust substitution maps, which are required
   * for storing proofs.
   */
  context::CDList<std::shared_ptr<theory::TrustSubstitutionMap> > d_tsubsList;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
