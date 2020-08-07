/*********************                                                        */
/*! \file proof_cnf_stream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include "theory/eager_proof_generator.h"

namespace CVC4 {
namespace prop {

/**
 * A layer on top of CNF stream. The goal of this class is manage the
 * use of a CNF stream object in such a way that the proper proofs are
 * internally constructed, and can be retrieved from this class when
 * necessary.
 *
 * It tracks the reason for why all clausification facts are added to an
 * underlying SAT solver in a user-context dependent manner in a
 * context-dependent (CDProof) object.
 *
 * A user of a SAT solver that is proof producing and uses the CNF stream may
 * use this class to manage proofs that are justified by its underlying CNF
 * stream.
 */
class ProofCnfStream : public ProofGenerator
{
 public:
  ProofCnfStream(context::UserContext* u,
                 CnfStream& cnfStream,
                 ProofNodeManager* pnm,
                 bool pfEnabled = true);
  ~ProofCnfStream() {}

  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  bool hasProofFor(Node f) override;
  /** identify */
  std::string identify() const override;

  /**
   * Converts and asserts a formula.
   * @param node node to convert and assert
   * @param negated whether we are asserting the node negated
   * @param removable whether the sat solver can choose to remove the clauses
   */
  void convertAndAssert(TNode node,
                        bool negated,
                        bool removable,
                        ProofGenerator* pg);

  /** Does the CNF convertion of the propagation lemma *without* registering the
   * resoluting clause in the SAT solver, as this is handled internally by the
   * SAT solver */
  void convertPropagation(theory::TrustNode ttn);

  /**
   * Ensure that the given node will have a designated SAT literal that is
   * definitionally equal to it. The result of this function is that the Node
   * can be queried via getSatValue(). Essentially, this is like a "convert-but-
   * don't-assert" version of convertAndAssert().
   */
  void ensureLiteral(TNode n, bool noPreregistration = false);

  /**
   * Transforms the node into CNF recursively.
   * @param node the formula to transform
   * @param negated whether the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);

  /**
   * Normalizes a clause (an OR node) according to factoring and reordering,
   * i.e. removes duplicates and reorders literals (according to node
   * ids). Moreover it eliminates double negations, which can be done also for
   * unit clauses. All normalization steps are tracked via proof step added to
   * the given proof.
   *
   * @param n the clause to be normalized
   * @param p the proof to which steps corresponding to the normalization will
   * be added
   */
  static Node factorReorderElimDoubleNeg(Node n, CDProof* p);

  /**
   * Eliminate double negation of a literal if it has the form (not (not t)). If
   * the elimination happens, a step is added to the given proof.
   *
   * @param n the node to have the top-level double negation eliminated
   * @param p the proof to which steps corresponding to the normalization will
   * be added
   */
  static Node elimDoubleNegLit(Node n, CDProof* p);

 private:
  /**
   * Same as above, except that removable is remembered.
   */
  void convertAndAssert(TNode node, bool negated);
  // Each of these formulas handles takes care of a Node of each Kind.
  //
  // Each handleX(Node &n) is responsible for:
  //   - constructing a new literal, l (if necessary)
  //   - calling registerNode(n,l)
  //   - adding clauses assure that l is equivalent to the Node
  //   - calling toCNF on its children (if necessary)
  //   - returning l
  //
  // handleX( n ) can assume that n is not in d_translationCache
  SatLiteral handleNot(TNode node);
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  void convertAndAssertAnd(TNode node, bool negated);
  void convertAndAssertOr(TNode node, bool negated);
  void convertAndAssertXor(TNode node, bool negated);
  void convertAndAssertIff(TNode node, bool negated);
  void convertAndAssertImplies(TNode node, bool negated);
  void convertAndAssertIte(TNode node, bool negated);

  /** Reference to the equality engine */
  CnfStream& d_cnfStream;
  /** the proof node manager */
  ProofNodeManager* d_pnm;
  /** The User-context-dependent proof object */
  LazyCDProof d_proof;
  /** The default proof generator (for simple facts) */
  /**
   * Whether proofs are enabled. If this flag is false, then this class acts
   * as a simplified interface to the EqualityEngine, without proofs.
   */
  bool d_pfEnabled;

  /**
   * Are we asserting a removable clause (true) or a permanent clause (false).
   * This is set at the beginning of convertAndAssert so that it doesn't
   * need to be passed on over the stack.  Only pure clauses can be asserted
   * as removable.
   */
  bool d_removable;
};

}  // namespace prop
}  // namespace CVC4

#endif
