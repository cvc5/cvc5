/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager of SmtEngine
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PROOF_MANAGER_H
#define CVC4__SMT__PROOF_MANAGER_H

#include "context/cdlist.h"
#include "expr/expr.h"
#include "expr/node.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "smt/preprocess_proof_generator.h"
#include "smt/proof_post_processor.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

class Assertions;

/**
 * This class is responsible for managing the proof output of SmtEngine, as
 * well as setting up the global proof checker and proof node manager.
 */
class PfManager
{
 public:
  PfManager(SmtEngine* smte);
  ~PfManager();
  /**
   * Print the proof on the output channel of the current options in scope.
   *
   * The argument pg is the module that can provide a proof for false in the
   * current context.
   *
   * Throws an assertion failure if pg cannot provide a closed proof with
   * respect to assertions in as.
   */
  void printProof(ProofGenerator* pg, Assertions& as);
  /**
   * Check proof, same as above, without printing.
   */
  void checkProof(ProofGenerator* pg, Assertions& as);

  /**
   * Get final proof.
   *
   * The argument pg is the module that can provide a proof for false in the
   * current context.
   */
  std::shared_ptr<ProofNode> getFinalProof(ProofGenerator* pg, Assertions& as);
  //--------------------------- access to utilities
  /** Get a pointer to the ProofChecker owned by this. */
  ProofChecker* getProofChecker() const;
  /** Get a pointer to the ProofNodeManager owned by this. */
  ProofNodeManager* getProofNodeManager() const;
  /** Get the proof generator for proofs of preprocessing. */
  smt::PreprocessProofGenerator* getPreprocessProofGenerator() const;
  //--------------------------- end access to utilities
 private:
  /**
   * Set final proof, which initializes d_finalProof to the proof of false
   * from pg, postprocesses it, and stores it in d_finalProof.
   */
  void setFinalProof(ProofGenerator* pg, context::CDList<Node>* al);
  /** The false node */
  Node d_false;
  /** For the new proofs module */
  std::unique_ptr<ProofChecker> d_pchecker;
  /** A proof node manager based on the above checker */
  std::unique_ptr<ProofNodeManager> d_pnm;
  /** The preprocess proof generator. */
  std::unique_ptr<smt::PreprocessProofGenerator> d_pppg;
  /** The proof post-processor */
  std::unique_ptr<smt::ProofPostproccess> d_pfpp;
  /**
   * The final proof produced by the SMT engine.
   * Combines the proofs of preprocessing, prop engine and theory engine, to be
   * connected by setFinalProof().
   */
  std::shared_ptr<ProofNode> d_finalProof;
}; /* class SmtEngine */

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__PROOF_MANAGER_H */
