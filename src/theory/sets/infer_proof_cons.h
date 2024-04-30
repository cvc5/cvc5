/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion for sets.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__INFER_PROOF_CONS_H
#define CVC5__THEORY__SETS__INFER_PROOF_CONS_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "theory/sets/inference.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

/**
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 */
class InferProofCons : protected EnvObj, public ProofGenerator
{
 public:
  InferProofCons(Env& env, context::Context* c);
  s
      /**
       * This is called to notify that di is an inference that may need a proof
       * in the future.
       *
       * In detail, this class should be prepared to respond to a call to:
       *   getProofFor(di.d_conc)
       * in the remainder of the SAT context. This method copies di and stores
       * it in the context-dependent map d_lazyFactMap below.
       *
       * This is used for lazy proof construction, where proofs are constructed
       * only for facts that are explained.
       */
      void
      notifyFact();

  /**
   * This returns the proof for fact. This is required for using this class as
   * a lazy proof generator.
   *
   * It should be the case that a call was made to notifyFact(di) where
   * di.d_conc is fact in this SAT context.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const override;

 private:
  /** Common constants */
  Node d_tdid;
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__INFER_PROOF_CONS_H */
