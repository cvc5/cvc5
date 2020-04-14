/*********************                                                        */
/*! \file proof_node.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof node utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_NODE_H
#define CVC4__EXPR__PROOF_NODE_H

#include <vector>

#include "expr/node.h"
#include "expr/proof_step.h"

namespace CVC4 {

class ProofNodeManager;

/** A node in a proof
 *
 * A ProofNode represents a single step in a proof. It contains:
 * (1) d_id, an identifier indicating the type of inference,
 * (2) d_children, the child ProofNode objects indicating its premises,
 * (3) d_args, additional arguments used to determine the conclusion,
 * (4) d_proven, cache of the formula that this ProofNode proves.
 *
 * Overall, a ProofNode and its children form a directed acyclic graph.
 *
 * A ProofNode is intended to be mutable in that (1), (2) and (3) can be
 * modified. An example is when a ProofNode is established to be a "hole"
 * for something to be proven later. However, (4) is intended to be immutable.
 *
 * The method setValue is private and can be called by objects that manage
 * ProofNode objects in trusted ways that ensure that the node maintains
 * the invariant above. Furthermore, notice that this class is not responsible
 * for setting d_proven; this is done externally by a ProofNodeManager class.
 */
class ProofNode
{
  friend class ProofNodeManager;

 public:
  ProofNode(ProofStep id,
            const std::vector<std::shared_ptr<ProofNode>>& children,
            const std::vector<Node>& args);
  ~ProofNode() {}
  /** get the id of this proof node */
  ProofStep getId() const;
  /** Get children */
  const std::vector<std::shared_ptr<ProofNode>>& getChildren() const;
  /** Get arguments */
  const std::vector<Node>& getArguments() const;
  /** get what this node proves, or the null node if this is an invalid proof */
  Node getResult() const;
  /** Get assumptions
   *
   * This adds to the vector assump all formulas that are "assumptions" of the
   * given proof. An assumption is a formula that is the argument of a
   * proof node whose kind is ASSUME.
   */
  void getAssumptions(std::vector<Node>& assump) const;
  /** Print debug on output strem os */
  void printDebug(std::ostream& os) const;

 private:
  /**
   * Set value, called to overwrite the contents of this ProofNode with the
   * given arguments.
   */
  void setValue(ProofStep id,
                const std::vector<std::shared_ptr<ProofNode>>& children,
                const std::vector<Node>& args);
  /** The proof step */
  ProofStep d_id;
  /** The children of this proof node */
  std::vector<std::shared_ptr<ProofNode>> d_children;
  /** arguments of this node */
  std::vector<Node> d_args;
  /** The cache of the fact that has been proven, modifiable by ProofChecker */
  Node d_proven;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_NODE_H */
