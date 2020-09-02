/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arrays inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__INFERENCE_MANAGER_H
#define CVC4__THEORY__ARRAYS__INFERENCE_MANAGER_H

#include "expr/node.h"
#include "expr/proof_rule.h"
#include "theory/theory_inference_manager.h"

namespace CVC4 {
namespace theory {
namespace arrays {

/**
 * The arrays inference manager.
 */
class InferenceManager : public TheoryInferenceManager
{
 public:
  InferenceManager(Theory& t, TheoryState& state, ProofNodeManager* pnm);
  ~InferenceManager() {}

  /** 
   * Assert inference. This sends an internal fact to the equality engine
   * immediately, possibly with proof support. The identifier id which
   * rule to apply when proofs are enabled. The order of children
   * and arguments to use in the proof step are determined internally in
   * this method.
   * 
   * @return true if the fact was successfully asserted, and false if the
   * fact was redundant.
   */
  bool assertInference(TNode atom, bool polarity, TNode reason, PfRule id);
};

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

#endif
