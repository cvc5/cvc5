/*********************                                                        */
/*! \file non_clausal_simp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Non-clausal simplification preprocessing pass.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__NON_CLAUSAL_SIMP_H
#define CVC4__PREPROCESSING__PASSES__NON_CLAUSAL_SIMP_H

#include <vector>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/preprocess_proof_generator.h"
#include "theory/trust_node.h"

namespace CVC4 {
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
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
  /** Is proof enabled? */
  bool isProofEnabled() const;
  /**
   * Add learned literal to the preprocess proof generator maintained by this
   * class.
   */
  void assertLearnedLiteral(const std::vector<Node>& assertions,
                            theory::TrustNode tll);
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** the learned literal preprocess proof generator */
  std::unique_ptr<smt::PreprocessProofGenerator> d_llpg;
  /**
   * An eager proof generator for automatically inferred proofs of learned
   * literals.
   */
  std::unique_ptr<theory::EagerProofGenerator> d_llRCons;
  /**
   * A context-dependent list of trust substitution maps, which are required
   * for storing proofs.
   */
  context::CDList<std::shared_ptr<theory::TrustSubstitutionMap> > d_tsubsList;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
