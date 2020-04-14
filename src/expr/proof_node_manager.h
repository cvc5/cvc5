/*********************                                                        */
/*! \file proof_node_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof node manager utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_NODE_MANAGER_H
#define CVC4__EXPR__PROOF_NODE_MANAGER_H

#include <vector>

#include "expr/proof_checker.h"
#include "expr/proof_node.h"

namespace CVC4 {

/**
 * A manager for proof node objects. This is a trusted way of creating
 * and updating ProofNode objects.
 */
class ProofNodeManager
{
 public:
  ProofNodeManager(ProofChecker* pc);
  ~ProofNodeManager() {}
  /**
   * Make proof node
   *
   */
  std::shared_ptr<ProofNode> mkProofNode(ProofStep id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args,
                                         Node expected = Node::null());
  /**
   * Update proof node
   *
   */
  void updateProofNode(ProofNode* pn,
                       ProofStep id,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args,
                       Node expected = Node::null());

 private:
  /** The (optional) proof checker */
  ProofChecker* d_checker;
  /** Check internal */
  bool checkInternal(ProofNode* pn, bool doCheck, bool doUpdate, Node expected);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_NODE_H */
