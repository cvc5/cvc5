/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arrays inference manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__INFERENCE_MANAGER_H
#define CVC5__THEORY__ARRAYS__INFERENCE_MANAGER_H

#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof_rule.h"
#include "theory/theory_inference_manager.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * The arrays inference manager.
 */
class InferenceManager : public TheoryInferenceManager
{
 public:
  InferenceManager(Env& env, Theory& t, TheoryState& state);
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
  bool assertInference(TNode atom, bool polarity, InferenceId id, TNode reason, PfRule pfr);
  /**
   * Send lemma (exp => conc) based on proof rule id with properties p.
   */
  bool arrayLemma(Node conc,
                  InferenceId id,
                  Node exp,
                  PfRule pfr,
                  LemmaProperty p = LemmaProperty::NONE);

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
}  // namespace cvc5::internal

#endif
