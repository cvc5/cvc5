/*********************                                                        */
/*! \file non_clausal_simp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Non-clausal simplification preprocessing pass.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__NON_CLAUSAL_SIMP_H
#define __CVC4__PREPROCESSING__PASSES__NON_CLAUSAL_SIMP_H

#include <vector>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

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
    TimerStat d_cnfTranslateTime;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

  /** Learned literals */
  std::vector<Node> d_nonClausalLearnedLiterals;

  /** Preprocess the boolean skeleton using CryptoMinisat
      Args:
      - assertionsToPreprocess: Top level assertions
      - substs_index: the substitution index in the current context
      Return:
      whether the boolean skeleton is not satisfiable and the
      learned unit clauses
   */
  std::pair<bool, std::vector<Node>> preprocessByCryptoMinisat(
      AssertionPipeline* assertionsToPreprocess, unsigned substs_index);

  /** Preprocess the boolean skeleton using CryptoMinisat
      Args:
      - assertionsToPreprocess: Top level assertions
      - substs_index: the substitution index in the current context
      Return:
      whether the boolean skeleton is not satisfiable and the
      learned unit clauses
   */
  std::pair<bool, std::vector<Node>> preprocessByCircuitPropagator(
      AssertionPipeline* assertionsToPreprocess, unsigned substs_index);

  /** Handle the case that a conflict in the boolean skeleton is detected */
  inline void handleConflictCase(AssertionPipeline* assertionsToPreprocess)
  {
    Trace("non-clausal-simplify")
        << "conflict in non-clausal propagation" << std::endl;
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    assertionsToPreprocess->clear();
    Node n = NodeManager::currentNM()->mkConst<bool>(false);
    assertionsToPreprocess->push_back(n);
    PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
  }
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
