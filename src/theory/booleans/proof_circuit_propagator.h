/*********************                                                        */
/*! \file proof_circuit_propagator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proofs for the non-clausal circuit propagator.
 **
 ** Proofs for the non-clausal circuit propagator.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BOOLEANS__PROOF_CIRCUIT_PROPAGATOR_H
#define CVC4__THEORY__BOOLEANS__PROOF_CIRCUIT_PROPAGATOR_H

#include <memory>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {
namespace theory {
namespace booleans {

/**
 * Base class for for CircuitPropagatorProofs.
 * This class collects common functionality for proofs of backward and forward
 * propagation.
 */
class ProofCircuitPropagator
{
 public:
  ProofCircuitPropagator(ProofNodeManager* pnm);
  
  /** Assuming the given node */
  std::shared_ptr<ProofNode> assume(Node n);

  /** (and true ... holdout true ...)  -->  holdout */
  std::shared_ptr<ProofNode> andFalse(Node parent, TNode::iterator holdout);

  /** (or false ... holdout false ...)  ->  holdout */
  std::shared_ptr<ProofNode> orTrue(Node parent, TNode::iterator holdout);

  /** (not x) is true  -->  x is false (and vice versa) */
  std::shared_ptr<ProofNode> Not(bool negate, Node parent);

  /** (=> X false)  -->  (not X) */
  std::shared_ptr<ProofNode> impliesXFromY(Node parent);
  /** (=> true Y)  -->  Y */
  std::shared_ptr<ProofNode> impliesYFromX(Node parent);

  /** Derive X from (= X Y) */
  std::shared_ptr<ProofNode> eqXFromY(bool y, Node Parent);
  /** Derive Y from (= X Y) */
  std::shared_ptr<ProofNode> eqYFromX(bool x, Node Parent);
  /** Derive X from (not (= X Y)) */
  std::shared_ptr<ProofNode> neqXFromY(bool y, Node parent);
  /** Derive Y from (not (= X Y)) */
  std::shared_ptr<ProofNode> neqYFromX(bool x, Node parent);

  /**
   * Uses (xor X Y) to derive the value of X.
   * (xor X false)  -->  X
   * (xor X true)  -->  (not X)
   * (not (xor X false))  -->  (not X)
   * (not (xor X true))  -->  X
   */
  std::shared_ptr<ProofNode> xorXFromY(bool negated, bool y, Node parent);
  /**
   * Uses (xor X Y) to derive the value of Y.
   * (xor false Y)  -->  Y
   * (xor true Y)  -->  (not Y)
   * (not (xor false Y))  -->  (not Y)
   * (not (xor true Y))  -->  Y
   */
  std::shared_ptr<ProofNode> xorYFromX(bool negated, bool x, Node parent);

 protected:
  /** Shorthand to check whether proof generation is disabled */
  bool disabled() const;

  /** Construct proof using the given rule, children and args */
  std::shared_ptr<ProofNode> mkProof(
      PfRule rule,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args = {});
  /** Apply CONTRA rule. Takes care of switching a and b if necessary */
  std::shared_ptr<ProofNode> mkContra(const std::shared_ptr<ProofNode>& a,
                                      const std::shared_ptr<ProofNode>& b);
  /**
   * Apply CHAIN_RESOLUTION rule.
   * Constructs the args from the given literals and polarities (called ids in
   * the proof rule). Automatically adds the clauses to resolve with as
   * assumptions, depending on their polarity.
   */
  std::shared_ptr<ProofNode> mkResolution(std::shared_ptr<ProofNode> clause,
                                          const std::vector<Node>& lits,
                                          const std::vector<bool>& polarity);
  /** Shorthand for mkResolution(clause, lits, {polarity, ...}) */
  std::shared_ptr<ProofNode> mkResolution(std::shared_ptr<ProofNode> clause,
                                          const std::vector<Node>& lits,
                                          bool polarity);
  /** Apply NOT_NOT_ELIM rule if n.getResult() is a nested negation */
  std::shared_ptr<ProofNode> mkNot(const std::shared_ptr<ProofNode>& n);

  /** The proof node manager */
  ProofNodeManager* d_pnm;
};

/** Proof generator for backward propagation */
class ProofCircuitPropagatorBackward : public ProofCircuitPropagator
{
 public:
  ProofCircuitPropagatorBackward(ProofNodeManager* pnm,
                                 TNode parent,
                                 bool parentAssignment);

  /** and true  -->  child is true */
  std::shared_ptr<ProofNode> andTrue(TNode::iterator i);

  /** or false  -->  child is false */
  std::shared_ptr<ProofNode> orFalse(TNode::iterator i);

  /**
   * Propagate on ite with evaluate condition
   * (ite true t e)  -->  t
   * (not (ite true t e))  -->  (not t)
   * (ite false t e)  -->  e
   * (not (ite false t e))  -->  (not e)
   */
  std::shared_ptr<ProofNode> iteC(bool c);
  /**
   * For (ite c t e), we can derive the value for c
   * c = 1: c = true
   * c = 0: c = false
   */
  std::shared_ptr<ProofNode> iteIsCase(unsigned c);

  /** (not (=> X Y))  -->  X */
  std::shared_ptr<ProofNode> impliesNegX();
  /** (not (=> X Y))  -->  (not Y) */
  std::shared_ptr<ProofNode> impliesNegY();

 private:
  TNode d_parent;
  bool d_parentAssignment;
};

/** Proof generator for forward propagation */
class ProofCircuitPropagatorForward : public ProofCircuitPropagator
{
 public:
  ProofCircuitPropagatorForward(ProofNodeManager* pnm,
                                Node child,
                                bool childAssignment,
                                Node parent);

  /** All children are true  -->  and is true */
  std::shared_ptr<ProofNode> andAllTrue();
  /** One child is false  -->  and is false */
  std::shared_ptr<ProofNode> andOneFalse();

  /** One child is true  -->  or is true */
  std::shared_ptr<ProofNode> orOneTrue();
  /** or false  -->  all children are false */
  std::shared_ptr<ProofNode> orFalse();

  /** Evaluate (ite true X _) from X */
  std::shared_ptr<ProofNode> iteEvalThen(bool x);
  /** Evaluate (ite false _ Y) from Y */
  std::shared_ptr<ProofNode> iteEvalElse(bool y);

  /** Evaluate (= X Y) from X,Y */
  std::shared_ptr<ProofNode> eqEval();

  /** Evaluate (=> X Y) from X,Y */
  std::shared_ptr<ProofNode> impliesEval(bool premise, bool conclusion);
  /** Evaluate (xor X Y) from X,Y */
  std::shared_ptr<ProofNode> xorEval(bool x, bool y);

 private:
  Node d_child;
  bool d_childAssignment;
  Node d_parent;
};

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

#endif
