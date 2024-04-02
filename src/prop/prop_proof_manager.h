/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "proof/lazy_proof.h"
#include "proof/proof_node_manager.h"
#include "prop/proof_cnf_stream.h"
#include "prop/proof_post_processor.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

class CDCLTSatSolver;
class CnfStream;
class SatProofManager;

/**
 * This class is responsible for managing the proof output of PropEngine, both
 * building and checking it.
 *
 * The expected proof to be built is a refutation proof with preprocessed
 * assertions as free assumptions.
 */
class PropPfManager : protected EnvObj
{
  friend class SatProofManager;

 public:
  PropPfManager(Env& env, CDCLTSatSolver* satSolver, CnfStream& cnfProof);
  /**
   * Ensure that the given node will have a designated SAT literal that is
   * definitionally equal to it.  The result of this function is that the Node
   * can be queried via getSatValue(). Essentially, this is like a "convert-but-
   * don't-assert" version of convertAndAssert().
   */
  void ensureLiteral(TNode n);

  /**
   * Converts a formula into CNF into CNF and asserts the generated clauses into
   * the underlying SAT solver of d_cnfStream. Every transformation the formula
   * goes through is saved as a concrete step in d_proof. This method makes a
   * call to the convertAndAssert method of d_pfCnfStream.
   *
   * @param node formula to convert and assert
   * @param negated whether we are asserting the node negated
   * @param removable whether the SAT solver can choose to remove the clauses
   * @param input whether the node is from the input
   * @param pg a proof generator for node
   */
  void convertAndAssert(
      TNode node, bool negated, bool removable, bool input, ProofGenerator* pg);
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

  /** Return lemmas used in the SAT proof. */
  std::vector<Node> getUnsatCoreLemmas();

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

  /** Normalizes a clause node and registers it in the SAT proof manager.
   *
   * Normalization (factoring, reordering, double negation elimination) is done
   * via the TheoryProofStepBuffer of this class, which will register the
   * respective steps, if any. This normalization is necessary so that the
   * resulting clauses of the clausification process are synchronized with the
   * clauses used in the underlying SAT solver, which automatically performs the
   * above normalizations on all added clauses.
   *
   * @param clauseNode The clause node to be normalized.
   * @return The normalized clause node.
   */
  Node normalizeAndRegister(TNode clauseNode,
                            bool input,
                            bool doNormalize = true);
  /**
   * Clausifies the given propagation lemma *without* registering the resulting
   * clause in the SAT solver, as this is handled internally by the SAT
   * solver. The clausification steps and the generator within the trust node
   * are saved in d_proof if we are producing proofs in the theory engine.
   */
  void notifyExplainedPropagation(TrustNode ttn);
  /**
   * Get the last explained propagation by the above method. This is required
   * only for Minisat.
   */
  Node getLastExplainedPropagation() const;
  /**
   * Reset the tracker for the last explained propagation. This is required only
   * for Minisat.
   */
  void resetLastExplainedPropagation();
  /**
   * Get the clausification proof of all clauses that have been sent to the SAT
   * solver.
   */
  LazyCDProof* getCnfProof();

 private:
  /** Retrieve the proofs for clauses derived from the input */
  std::vector<std::shared_ptr<ProofNode>> getInputClausesProofs();
  /** Retrieve the proofs for clauses derived from lemmas */
  std::vector<std::shared_ptr<ProofNode>> getLemmaClausesProofs();
  /** Retrieve the clauses derived from the input */
  std::vector<Node> getInputClauses();
  /** Retrieve the clauses derived from lemmas */
  std::vector<Node> getLemmaClauses();
  /**
   * Get auxilary units. Computes top-level formulas in clauses that
   * also occur as literals which we call "auxiliary units". In particular,
   * consider the set of propositionally unsatisfiable clauses:
   *
   * (or ~(or A B) ~C)
   * (or A B)
   * C
   *
   * Here, we return (or A B) as an auxilary unit clause.
   *
   * Note that in the above example, it is ambiguous whether to interpret the
   * second clause (or A B) as a unit clause or as a clause with literals
   * A and B. To ensure that we generate an unsatisfiable DIMACS, we include
   * both in a proof output. In particular, Any OR-term that occurs as a literal
   * of another clause is included in the return vector.
   *
   * @param clauses The clauses
   * @return the auxiliary units for the set of clauses.
   */
  std::vector<Node> computeAuxiliaryUnits(const std::vector<Node>& clauses);
  /** The proofs of this proof manager, which are saved once requested (note the
   * cache is for both the request of the full proof (true) or not (false)).
   *
   * The proofs are kept in a (user)context-dependent manner because between
   * satisfiability checks we should discard them.
   */
  context::CDHashMap<bool, std::shared_ptr<ProofNode>> d_propProofs;
  /** The user-context-dependent proof object. */
  LazyCDProof d_proof;
  /** The proof post-processor */
  std::unique_ptr<prop::ProofPostprocess> d_pfpp;
  /** Proof-producing CNF converter */
  ProofCnfStream d_pfCnfStream;
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
  CnfStream& d_cnfStream;
  /** Asserted clauses derived from the input */
  context::CDHashSet<Node> d_inputClauses;
  /** Asserted clauses derived from lemmas */
  context::CDHashSet<Node> d_lemmaClauses;
  /** The current propagation being processed via this class. */
  Node d_currPropagationProcessed;
  /** Temporary, pointer to SAT proof manager */
  SatProofManager* d_satPm;
}; /* class PropPfManager */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PROOF_MANAGER_H */
