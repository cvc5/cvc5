/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Hans-Jörg
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof node utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_NODE_H
#define CVC5__PROOF__PROOF_NODE_H

#include <vector>

#include "expr/node.h"
#include "proof/proof_rule.h"

namespace cvc5::internal {

class ProofNodeManager;
class ProofNode;

// Alias for shared pointer to a proof node
using Pf = std::shared_ptr<ProofNode>;

struct ProofNodeHashFunction
{
  inline size_t operator()(std::shared_ptr<ProofNode> pfn) const;
  size_t operator()(const ProofNode* pfn) const;
}; /* struct ProofNodeHashFunction */

/** A node in a proof
 *
 * A ProofNode represents a single step in a proof. It contains:
 * (1) d_id, an identifier indicating the kind of inference,
 * (2) d_children, the child ProofNode objects indicating its premises,
 * (3) d_args, additional arguments used to determine the conclusion,
 * (4) d_proven, cache of the formula that this ProofNode proves.
 *
 * Overall, a ProofNode and its children form a directed acyclic graph.
 *
 * A ProofNode is partially mutable in that (1), (2) and (3) can be
 * modified. A motivating example of when this is useful is when a ProofNode
 * is established to be a "hole" for something to be proven later. On the other
 * hand, (4) is intended to be immutable.
 *
 * The method setValue is private and can be called by objects that manage
 * ProofNode objects in trusted ways that ensure that the node maintains
 * the invariant above. Furthermore, notice that this class is not responsible
 * for setting d_proven; this is done externally by a ProofNodeManager class.
 *
 * Notice that all fields of ProofNode are stored in ***Skolem form***. Their
 * correctness is checked in ***witness form*** (for details on this
 * terminology, see expr/skolem_manager.h). As a simple example, say a
 * theory solver has a term t, and wants to introduce a unit lemma (= k t)
 * where k is a fresh Skolem variable. It creates this variable via:
 *   k = SkolemManager::mkPurifySkolem(t,"k");
 * A checked ProofNode for the fact (= k t) then may have fields:
 *   d_rule := MACRO_SR_PRED_INTRO,
 *   d_children := {},
 *   d_args := {(= k t)}
 *   d_proven := (= k t).
 * Its justification via the rule MACRO_SR_PRED_INTRO (see documentation
 * in theory/builtin/proof_kinds) is in terms of the witness form of the
 * argument:
 *   (= (witness ((z T)) (= z t)) t)
 * which, by that rule's side condition, is such that:
 *   Rewriter::rewrite((= (witness ((z T)) (= z t)) t)) = true.
 * Notice that the correctness of the rule is justified here by rewriting
 * the witness form of (= k t). The conversion to/from witness form is
 * managed by ProofRuleChecker::check.
 *
 * An external proof checker is expected to formalize the ProofNode only in
 * terms of *witness* forms.
 *
 * However, the rest of cvc5 sees only the *Skolem* form of arguments and
 * conclusions in ProofNode, since this is what is used throughout cvc5.
 */
class ProofNode
{
  friend class ProofNodeManager;

 public:
  ProofNode(PfRule id,
            const std::vector<std::shared_ptr<ProofNode>>& children,
            const std::vector<Node>& args);
  ~ProofNode() {}
  /** get the rule of this proof node */
  PfRule getRule() const;
  /** Get children */
  const std::vector<std::shared_ptr<ProofNode>>& getChildren() const;
  /** Get arguments */
  const std::vector<Node>& getArguments() const;
  /** get what this node proves, or the null node if this is an invalid proof */
  Node getResult() const;
  /**
   * Returns true if this is a closed proof (i.e. it has no free assumptions).
   */
  bool isClosed();
  /** Print debug on output strem os
   *
   * @param os the stream to print to
   * @param printConclusion Whether to print conclusions
   */
  void printDebug(std::ostream& os, bool printConclusion = false) const;
  /**
   * Clone this proof node, which creates a deep copy of this proof node and
   * returns it. The dag structure of pn is the same as that in the returned
   * proof node.
   *
   * @return the cloned proof node.
   */
  std::shared_ptr<ProofNode> clone() const;

 private:
  /**
   * Set value, called to overwrite the contents of this ProofNode with the
   * given arguments.
   */
  void setValue(PfRule id,
                const std::vector<std::shared_ptr<ProofNode>>& children,
                const std::vector<Node>& args);
  /** The proof rule */
  PfRule d_rule;
  /** The children of this proof node */
  std::vector<std::shared_ptr<ProofNode>> d_children;
  /** arguments of this node */
  std::vector<Node> d_args;
  /** The cache of the fact that has been proven, modifiable by ProofChecker */
  Node d_proven;
  /** Was d_proven actually checked, or is it trusted? */
  bool d_provenChecked;
};

inline size_t ProofNodeHashFunction::operator()(
    std::shared_ptr<ProofNode> pfn) const
{
  return pfn->getResult().getId() + static_cast<unsigned>(pfn->getRule());
}

/**
 * Serializes a given proof node to the given stream.
 *
 * @param out the output stream to use
 * @param pn the proof node to output to the stream
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const ProofNode& pn);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_NODE_H */
