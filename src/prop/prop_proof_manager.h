/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include <cvc5/cvc5_types.h>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "prop/proof_post_processor.h"
#include "prop/sat_proof_manager.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace prop {

class CDCLTSatSolver;

/**
 * This class is responsible for managing the proof output of PropEngine, both
 * building and checking it.
 *
 * The expected proof to be built is a refutation proof with preprocessed
 * assertions as free assumptions.
 */
class PropPfManager : protected EnvObj
{
 public:
  PropPfManager(Env& env,
                context::UserContext* userContext,
                CDCLTSatSolver* satSolver,
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
   *
   * @param connectCnf If this flag is false, then all clausified preprocessed
   * assertion and theory lemmas are free assumptions in the returned proof
   * instead of being connected to their proofs.
   */
  std::shared_ptr<ProofNode> getProof(bool connectCnf);

  /** Return the vector of proofs for the respective proof component requested.
   *
   * The components may be of theory lemma proofs (closed proofs of valid theory
   * clauses) or of preprocessed assertion proofs (them the preprocessed
   * assertion assumptions to the added clauses to the SAT solver).
   */
  std::vector<std::shared_ptr<ProofNode>> getProofLeaves(
      modes::ProofComponent pc);

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
  void checkProof(const context::CDList<Node>& assertions);

 private:
  /** The proofs of this proof manager, which are saved once requested (note the
   * cache is for both the request of the full proof (true) or not (false)).
   *
   * The proofs are kept in a (user)context-dependent manner because between
   * satisfiability checks we should discard them.
   */
  context::CDHashMap<bool, std::shared_ptr<ProofNode>> d_propProofs;
  /** The proof post-processor */
  std::unique_ptr<prop::ProofPostprocess> d_pfpp;
  /**
   * The SAT solver of this prop engine, which should provide a refutation
   * proof when requested */
  CDCLTSatSolver* d_satSolver;
  /** Assertions corresponding to the leaves of the prop engine's proof.
   *
   * These are kept in a context-dependent manner since the prop engine's proof
   * is also kept in a context-dependent manner.
   */
  context::CDList<Node> d_assertions;
  /** The cnf stream proof generator */
  ProofCnfStream* d_proofCnfStream;
}; /* class PropPfManager */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PROOF_MANAGER_H */
