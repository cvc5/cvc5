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

#include "context/cdhashmap.h"
#include "context/cdlist.h"
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
class DefinedFunction;

/**
 * This class is responsible for managing the proof output of SmtEngine, as
 * well as setting up the global proof checker and proof node manager.
 */
class PfManager
{
  /** The type of our internal map of defined functions */
  using DefinedFunctionMap =
      context::CDHashMap<Node, smt::DefinedFunction, NodeHashFunction>;

 public:
  PfManager(context::UserContext* u, SmtEngine* smte);
  ~PfManager();
  /**
   * Print the proof on the given output stream.
   *
   * The argument pfn is the proof for false in the current context.
   *
   * Throws an assertion failure if pg cannot provide a closed proof with
   * respect to assertions in as and df. For the latter, entries in the defined
   * function map correspond to equalities of the form (= f (lambda (...) t)),
   * which are considered assertions in the final proof.
   */
  void printProof(std::ostream& out,
                  std::shared_ptr<ProofNode> pfn,
                  Assertions& as,
                  DefinedFunctionMap& df);
  /**
   * Check proof, same as above, without printing.
   */
  void checkProof(std::shared_ptr<ProofNode> pfn,
                  Assertions& as,
                  DefinedFunctionMap& df);

  /**
   * Get final proof.
   *
   * The argument pfn is the proof for false in the current context.
   */
  std::shared_ptr<ProofNode> getFinalProof(std::shared_ptr<ProofNode> pfn,
                                           Assertions& as,
                                           DefinedFunctionMap& df);
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
   * Set final proof, which initializes d_finalProof to the given proof node of
   * false, postprocesses it, and stores it in d_finalProof.
   */
  void setFinalProof(std::shared_ptr<ProofNode> pfn,
                     Assertions& as,
                     DefinedFunctionMap& df);
  /**
   * Get assertions from the assertions
   */
  void getAssertions(Assertions& as,
                     DefinedFunctionMap& df,
                     std::vector<Node>& assertions);
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
