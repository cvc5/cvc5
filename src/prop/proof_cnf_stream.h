/*********************                                                        */
/*! \file proof_cnf_stream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof-producing CNF stream
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__PROOF_CNF_STREAM_H
#define CVC4__PROP__PROOF_CNF_STREAM_H

#include "context/cdhashmap.h"
#include "expr/lazy_proof.h"
#include "expr/node.h"
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "prop/cnf_stream.h"
#include "prop/sat_proof_manager.h"
#include "theory/eager_proof_generator.h"
#include "theory/theory_proof_step_buffer.h"

namespace CVC4 {
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
class ProofCnfStream : public ProofGenerator
{
 public:
  ProofCnfStream(context::UserContext* u,
                 CnfStream& cnfStream,
                 SatProofManager* satPM,
                 ProofNodeManager* pnm);

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
   * @param pg a proof generator for node
   */
  void convertAndAssert(TNode node,
                        bool negated,
                        bool removable,
                        ProofGenerator* pg);

  /**
   * Clausifies the given propagation lemma *without* registering the
   * resoluting clause in the SAT solver, as this is handled internally by the
   * SAT solver. The clausification steps and the generator within the trust
   * node are saved in d_proof. */
  void convertPropagation(theory::TrustNode ttn);

  /**
   * Blocks a proof, so that it is not further updated by a post processor of
   * this class's proof. */
  void addBlocked(std::shared_ptr<ProofNode> pfn);

  /**
   * Whether a given proof is blocked for further updates.  An example of a
   * blocked proof node is one integrated into this class via an external proof
   * generator. */
  bool isBlocked(std::shared_ptr<ProofNode> pfn);

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
  SatLiteral handleNot(TNode node);
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
   */
  void normalizeAndRegister(TNode clauseNode);
  /**
   * Are we asserting a removable clause (true) or a permanent clause (false).
   * This is set at the beginning of convertAndAssert so that it doesn't need to
   * be passed on over the stack. Only pure clauses can be asserted as
   * removable.
   */
  bool d_removable;
  /** Reference to the underlying cnf stream. */
  CnfStream& d_cnfStream;
  /** The proof manager of underlying SAT solver associated with this stream. */
  SatProofManager* d_satPM;
  /** The proof node manager. */
  ProofNodeManager* d_pnm;
  /** The user-context-dependent proof object. */
  LazyCDProof d_proof;
  /** An accumulator of steps that may be applied to normalize the clauses
   * generated during clausification. */
  theory::TheoryProofStepBuffer d_psb;
  /** Blocked proofs.
   *
   * These are proof nodes added to this class by external generators. */
  context::CDHashSet<std::shared_ptr<ProofNode>, ProofNodeHashFunction>
      d_blocked;
};

}  // namespace prop
}  // namespace CVC4

#endif
