/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
#include "theory/eager_proof_generator.h"
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
  /**
   * Send lemma (exp => conc) based on proof rule id with properties p. Cache
   * the lemma if doCache is true.
   */
  bool arrayLemma(Node conc,
                  Node exp,
                  PfRule id,
                  LemmaProperty p = LemmaProperty::NONE,
                  bool doCache = false);

 private:
  /**
   * Converts a conclusion, explanation and proof rule id used by the array
   * theory to the set of arguments required for a proof rule application.
   */
  void convert(PfRule& id,
               Node conc,
               Node exp,
               std::vector<Node>& children,
               std::vector<Node>& args);
  /** Eager proof generator for lemmas from the above method */
  std::unique_ptr<EagerProofGenerator> d_lemmaPg;
};

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

#endif
