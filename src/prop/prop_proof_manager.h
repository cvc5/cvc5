/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof manager of PropEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP_PROOF_MANAGER_H
#define CVC5__PROP_PROOF_MANAGER_H

#include "context/cdlist.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "prop/proof_post_processor.h"
#include "prop/sat_proof_manager.h"

namespace cvc5 {

namespace prop {

class CDCLTSatSolverInterface;

/**
 * This class is responsible for managing the proof output of PropEngine, both
 * building and checking it.
 *
 * The expected proof to be built is a refutation proof with preprocessed
 * assertions as free assumptions.
 */
class PropPfManager
{
 public:
  PropPfManager(context::UserContext* userContext,
                ProofNodeManager* pnm,
                CDCLTSatSolverInterface* satSolver,
                ProofCnfStream* cnfProof);

  /** Saves assertion for later checking whether refutation proof is closed.
   *
   * The assertions registered via this interface are preprocessed assertions
   * from SMT engine as they are asserted to the prop engine.
   */
  void registerAssertion(Node assertion);
  /**
   * Generates the prop engine proof: a proof of false resulting from the
   * connection of the refutation proof in d_satPM with the justification for
   * its assumptions, which are retrieved from the CNF conversion proof, if any.
   *
   * The connection is done by running the proof post processor d_pfpp over the
   * proof of false provided by d_satPM. See ProofPostProcessor for more
   * details.
   */
  std::shared_ptr<ProofNode> getProof();

  /**
   * Checks that the prop engine proof is closed w.r.t. the given assertions and
   * previously registered assertions in d_assertions.
   *
   * A common use of other assertions on top of the ones already registered on
   * d_assertions is checking closedness w.r.t. preprocessed *and* input
   * assertions. This is necessary if a prop engine's proof is modified
   * externally (which can happen, for example, when connecting the prop
   * engine's proof with the preprocessing proof) and these changes survive for
   * a next check-sat call.
   */
  void checkProof(context::CDList<Node>* assertions);

 private:
  /** A node manager */
  ProofNodeManager* d_pnm;
  /** The proof post-processor */
  std::unique_ptr<prop::ProofPostproccess> d_pfpp;
  /**
   * The SAT solver of this prop engine, which should provide a refutation
   * proof when requested */
  CDCLTSatSolverInterface* d_satSolver;
  /** Assertions corresponding to the leaves of the prop engine's proof.
   *
   * These are kept in a context-dependent manner since the prop engine's proof
   * is also kept in a context-dependent manner.
   */
  context::CDList<Node> d_assertions;
}; /* class PropPfManager */

}  // namespace prop
}  // namespace cvc5

#endif /* CVC5__PROP__PROOF_MANAGER_H */
