/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Dejan Jovanovic, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof-producing CNF stream.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__PROOF_CNF_STREAM_H
#define CVC5__PROP__PROOF_CNF_STREAM_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "prop/cnf_stream.h"
#include "prop/opt_clauses_manager.h"
#include "prop/sat_proof_manager.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

class SatProofManager;

/**
 * A proof generator for CNF transformation. It is a layer on top of CNF stream,
 * tracking the justifications for clauses added into the underlying SAT solver
 * in a user-context dependent manner in a lazy context-dependent (LazyCDProof)
 * object. The proof is lazy because formulas asserted to this class may also
 * take proof generators (which is the case, for example, for theory lemmas), so
 * that getting the proof of a clausified formula will also extend to its
 * registered proof generator.
 */
class ProofCnfStream : protected EnvObj, public ProofGenerator
{
 public:
  ProofCnfStream(Env& env, CnfStream& cnfStream, SatProofManager* satPM);

  /** Invokes getProofFor of the underlying LazyCDProof */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Whether there is a concrete step or a generator associated with f in the
   * underlying LazyCDProof. */
  bool hasProofFor(Node f) override;
  /** identify */
  std::string identify() const override;
  /**
   * Converts a formula into CNF into CNF and asserts the generated clauses into
   * the underlying SAT solver of d_cnfStream. Every transformation the formula
   * goes through is saved as a concrete step in d_proof.
   *
   * The given formula has arbitrary Boolean structure via kinds AND, OR, EQUAL,
   * XOR, IMPLIES. ITE and NOT. The conversion is done polynomially via Tseitin
   * transformation, with the children of non-conjunctive kinds being abstracted
   * as new literals, which are clausified with the respective "handle" methods
   * below.

   * @param node formula to convert and assert
   * @param negated whether we are asserting the node negated
   * @param removable whether the SAT solver can choose to remove the clauses
   * @param input whether the node is from the input
   * @param pg a proof generator for node
   */
  void convertAndAssert(TNode node,
                        bool negated,
                        bool removable,
                        bool input,
                        ProofGenerator* pg);

  /**
   * Clausifies the given propagation lemma *without* registering the resoluting
   * clause in the SAT solver, as this is handled internally by the SAT
   * solver. The clausification steps and the generator within the trust node
   * are saved in d_proof if we are producing proofs in the theory engine. */
  void convertPropagation(TrustNode ttn);
  /**
   * Ensure that the given node will have a designated SAT literal that is
   * definitionally equal to it.  The result of this function is that the Node
   * can be queried via getSatValue(). Essentially, this is like a "convert-but-
   * don't-assert" version of convertAndAssert().
   */
  void ensureLiteral(TNode n);

  /**
   * Returns true iff the node has an assigned literal (it might not be
   * translated).
   */
  bool hasLiteral(TNode node) const;

  /**
   * Returns the literal that represents the given node in the SAT CNF
   * representation.
   */
  SatLiteral getLiteral(TNode node);

  /**
   * Returns the Boolean variables from the input problem.
   */
  void getBooleanVariables(std::vector<TNode>& outputVariables) const;

  /**
   * Blocks a proof, so that it is not further updated by a post processor of
   * this class's proof. */
  void addBlocked(std::shared_ptr<ProofNode> pfn);

  /**
   * Whether a given proof is blocked for further updates.  An example of a
   * blocked proof node is one integrated into this class via an external proof
   * generator. */
  bool isBlocked(std::shared_ptr<ProofNode> pfn);

  /** Notify that current propagation inserted at lower level than current.
   *
   * The proof of the current propagation (d_currPropagationProcessed) will be
   * saved in d_optClausesPfs, so that it is not potentially lost when the user
   * context is popped.
   */
  void notifyCurrPropagationInsertedAtLevel(uint32_t explLevel);
  /** Notify that added clause was inserted at lower level than current.
   *
   * As above, the proof of this clause is saved in  d_optClausesPfs.
   */
  void notifyClauseInsertedAtLevel(const SatClause& clause, uint32_t clLevel);

  /** Retrieve the proofs for clauses derived from the input */
  std::vector<std::shared_ptr<ProofNode>> getInputClausesProofs();
  /** Retrieve the proofs for clauses derived from lemmas */
  std::vector<std::shared_ptr<ProofNode>> getLemmaClausesProofs();

  /** Retrieve the clauses derived from the input */
  std::vector<Node> getInputClauses();
  /** Retrieve the clauses derived from lemmas */
  std::vector<Node> getLemmaClauses();

 private:
  /**
   * Same as above, except that uses the saved d_removable flag. It calls the
   * dedicated converter for the possible formula kinds.
   */
  void convertAndAssert(TNode node, bool negated);
  /** Specific converters for each formula kind. */
  void convertAndAssertAnd(TNode node, bool negated);
  void convertAndAssertOr(TNode node, bool negated);
  void convertAndAssertXor(TNode node, bool negated);
  void convertAndAssertIff(TNode node, bool negated);
  void convertAndAssertImplies(TNode node, bool negated);
  void convertAndAssertIte(TNode node, bool negated);
  /**
   * Transforms the node into CNF recursively and yields a literal
   * definitionally equal to it.
   *
   * This method also populates caches, kept in d_cnfStream, between formulas
   * and literals to avoid redundant work and to retrieve formulas from literals
   * and vice-versa.
   *
   * @param node the formula to transform
   * @param negated whether the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);
  /**
   * Specific clausifiers, based on the formula kinds, that clausify a formula,
   * by calling toCNF into each of the formula's children under the respective
   * kind, and introduce a literal definitionally equal to it. */
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

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
  Node normalizeAndRegister(TNode clauseNode);

  /** Gets node equivalent to SAT clause.
   *
   * To avoid generating different nodes for the same clause, modulo ordering,
   * an invariant assumed throughout this class, the OR node generated by this
   * method always has its children ordered.
   */
  Node getClauseNode(const SatClause& clause);

  /** Reference to the underlying cnf stream. */
  CnfStream& d_cnfStream;

  /** Whether we are we asserting clauses derived from the input. */
  bool d_input;
  /** Asserted clauses derived from the input */
  context::CDHashSet<Node> d_inputClauses;
  /** Asserted clauses derived from lemmas */
  context::CDHashSet<Node> d_lemmaClauses;

  /** The proof manager of underlying SAT solver associated with this stream. */
  SatProofManager* d_satPM;
  /** The user-context-dependent proof object. */
  LazyCDProof d_proof;
  /** An accumulator of steps that may be applied to normalize the clauses
   * generated during clausification. */
  TheoryProofStepBuffer d_psb;
  /** Blocked proofs.
   *
   * These are proof nodes added to this class by external generators. */
  context::CDHashSet<std::shared_ptr<ProofNode>, ProofNodeHashFunction>
      d_blocked;

  /** The current propagation being processed via this class. */
  Node d_currPropagationProcessed;
  /** User-context-dependent map assertion level to proof nodes.
   *
   * This map is used to update the internal proof of this class when the
   * context pops.
   */
  std::map<int, std::vector<std::shared_ptr<ProofNode>>> d_optClausesPfs;
  /** Manager for optimized propagations and added clauses inserted at assertion
   * levels below the current user level. */
  OptimizedClausesManager d_optClausesManager;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif
