/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof manager of SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_MANAGER_H
#define CVC5__SMT__PROOF_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "options/proof_options.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofChecker;
class ProofNode;
class ProofNodeManager;
class SolverEngine;

namespace rewriter {
class RewriteDb;
}

namespace smt {

class Assertions;
class SmtSolver;
class PreprocessProofGenerator;
class ProofPostprocess;

/** Modes for global Proof scopes introducing definitions and assertions. */
enum class ProofScopeMode
{
  /** No global scopes. Open proof. */
  NONE,
  /** Proof closed by a unified scope introducing definitions and assertions. */
  UNIFIED,
  /** Proof closed by 2 nested scopes introducing definitions and assertions. */
  DEFINITIONS_AND_ASSERTIONS,
};

/**
 * This class is responsible for managing the proof output of SolverEngine, as
 * well as setting up the global proof checker and proof node manager.
 *
 * The proof production of an SolverEngine is directly impacted by whether, and
 * how, we are producing unsat cores:
 *
 * - If we are producing unsat cores using the old proof infrastructure, then
 *   SolverEngine will not have proofs in the sense of this proof manager.
 *
 * - If we are producing unsat cores using this proof infrastructure, then the
 *   SolverEngine will have proofs using this proof manager, according to the
 * unsat core mode:
 *
 *   - assumption mode: proofs only for preprocessing, not in sat solver or
 *   theory engine, and level of granularity set to off (unless otherwise
 *   specified by the user)
 *
 *   - sat-proof mode: proofs for preprocessing + sat solver, not in theory
 *   engine and level of granularity set to off (unless otherwise specified by
 *   the user)
 *
 *   - full-proof mode: proofs for the whole solver as normal
 *
 *   Note that if --produce-proofs is set then full-proof mode of unsat cores is
 *   forced.
 *
 * - If we are not producing unsat cores then the SolverEngine will have proofs
 * as long as --produce-proofs is on.
 *
 * - If SolverEngine has been configured in a way that is incompatible with
 * proofs then unsat core production will be disabled.
 */
class PfManager : protected EnvObj
{
 public:
  PfManager(Env& env);
  ~PfManager();
  /**
   * Print the proof on the given output stream in the given format.
   */
  void printProof(std::ostream& out,
                  std::shared_ptr<ProofNode> fp,
                  options::ProofFormatMode mode);

  /**
   * Translate difficulty map. This takes a mapping dmap from preprocessed
   * assertions to values estimating their difficulty. It translates this
   * map so that dmap contains a mapping from *input* assertions to values
   * estimating their difficulty.
   *
   * It does this translation by constructing a proof of preprocessing for all
   * preprocessed assertions marked as having a difficulty, traversing those
   * proofs, and conditionally incrementing the difficulty of the input
   * assertion on which they depend. This is based on whether the free
   * assumption is the "source" of an assertion.
   *
   * @param dmap Map estimating the difficulty of preprocessed assertions
   * @param smt The SMT solver that owns the assertions and the preprocess
   * proof generator.
   */
  void translateDifficultyMap(std::map<Node, Node>& dmap, SmtSolver& smt);

  /**
   * Connect proof to assertions
   *
   * Replaces the free assumptions of pfn that correspond to preprocessed
   * assertions maintained by smt with their corresponding proof of
   * preprocessing, which is obtained from the preprocessor of smt.
   *
   * Throws an assertion failure if pg cannot provide a closed proof with
   * respect to assertions in as. Note this includes equalities of the form
   * (= f (lambda (...) t)) which originate from define-fun commands for f.
   * These are considered assertions in the final proof.
   */
  std::shared_ptr<ProofNode> connectProofToAssertions(
      std::shared_ptr<ProofNode> pfn,
      SmtSolver& smt,
      ProofScopeMode scopeMode = ProofScopeMode::UNIFIED);
  //--------------------------- access to utilities
  /** Get a pointer to the ProofChecker owned by this. */
  ProofChecker* getProofChecker() const;
  /** Get a pointer to the ProofNodeManager owned by this. */
  ProofNodeManager* getProofNodeManager() const;
  /** Get the rewrite database, containing definitions of rewrites from DSL. */
  rewriter::RewriteDb* getRewriteDatabase() const;
  //--------------------------- end access to utilities
 private:
  /**
   * Get assertions from the assertions
   */
  void getAssertions(Assertions& as, std::vector<Node>& assertions);
  /**
   * Get definitions and assertions from the assertions
   */
  void getDefinitionsAndAssertions(Assertions& as,
                                   std::vector<Node>& definitions,
                                   std::vector<Node>& assertions);
  /** The false node */
  Node d_false;
  /** The rewrite proof database. */
  std::unique_ptr<rewriter::RewriteDb> d_rewriteDb;
  /** For the new proofs module */
  std::unique_ptr<ProofChecker> d_pchecker;
  /** A proof node manager based on the above checker */
  std::unique_ptr<ProofNodeManager> d_pnm;
  /** The proof post-processor */
  std::unique_ptr<smt::ProofPostprocess> d_pfpp;
}; /* class SolverEngine */

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__PROOF_MANAGER_H */
