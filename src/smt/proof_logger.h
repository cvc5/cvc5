/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof logger utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_LOGGER_H
#define CVC5__SMT__PROOF_LOGGER_H

#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

/**
 * The purpose of this class is to output proofs for all reasoning the solver
 * does on-the-fly. It is enabled when proof logging is enabled.
 *
 * This class receives notifications for three things:
 * (1) When preprocessing has completed, determining the set of input clauses.
 * (2) When theory lemmas are learned
 * (3) When a SAT refutation is derived.
 * 
 * Dependending on the proof mode, the notifications for the above three things
 * may be in the form of ProofNode (if proofs are enabled for that component),
 * or Node (if proofs are disabled for that component).
 * 
 * As with dumped proofs, the granularity of the proofs is subject to the
 * option `proof-granularity`.
 */
class ProofLogger : protected EnvObj
{
 public:
  /** */
  ProofLogger(Env& env) : EnvObj(env){}
  ~ProofLogger(){}
  /**
   * Called when preprocessing is complete with the list of input clauses,
   * after preprocessing and conversion to CNF.
   * @param input The list of input clauses.
   */
  virtual void logCnfPreprocessInputs(const std::vector<Node>& inputs) {}
  /**
   * Called when preprocessing is complete with the proofs of the preprocessed
   * inputs. The free assumptions of proofs in pfns are the preprocessed input
   * formulas. If preprocess proofs are avialable, this method connects pfn to
   * the original input formulas.
   * @param pfns Proofs of the preprocessed inputs.
   */
  virtual void logCnfPreprocessInputProofs(
      std::vector<std::shared_ptr<ProofNode>>& pfns) {}
  /**
   * Called when clause `n` is added to the SAT solver, where `n` is
   * (the CNF conversion of) a theory lemma.
   * @param n The theory lemma.
   */
  virtual void logTheoryLemma(const Node& n) {}
  /**
   * Called when clause `pfn` is added to the SAT solver, where `pfn`
   * is a closed proof of (the CNF conversion of) a theory lemma.
   * @param pfn The closed proof of a theory lemma.
   */
  virtual void logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn) {}
  /**
   * Called when the SAT solver derives false. The SAT refutation should be
   * derivable by propositional reasoning via the notified preprocessed input
   * and theory lemmas as given above.
   */
  virtual void logSatRefutation() {}

  /**
   * Called when the SAT solver generates a proof of false. The free assumptions
   * of this proof is the union of the CNF conversion of input and theory lemmas
   * as notified above.
   * @param pfn The refutation proof.
   */
  virtual void logSatRefutationProof(std::shared_ptr<ProofNode>& pfn) {}
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */
