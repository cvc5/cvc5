/*********************                                                        */
/*! \file proof_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof checker utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_CHECKER_H
#define CVC4__EXPR__PROOF_CHECKER_H

#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {

/** A virtual base class for checking a proof rule */
class ProofRuleChecker
{
 public:
  ProofRuleChecker() {}
  virtual ~ProofRuleChecker() {}
  /**
   * This checks a single step in a proof.
   *
   * Return the formula that is proven by a proof node with the given id,
   * premises and arguments, or null if such a proof node is not well-formed.
   *
   * @param id The id of the proof node to check
   * @param children The premises of the proof node to check. These are nodes
   * corresponding to the conclusion (ProofNode::getResult) of the children
   * of the proof node we are checking.
   * @param args The arguments of the proof node to check
   * @return The conclusion of the proof node if successful or null if such a
   * proof node is malformed.
   */
  virtual Node check(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) = 0;
};

/** A class for checking proofs */
class ProofChecker
{
 public:
  ProofChecker() {}
  ~ProofChecker() {}
  /**
   * Return the formula that is proven by proof node pn, or null if pn is not
   * well-formed. If expected is non-null, then we return null if pn does not
   * prove expected.
   *
   * @param pn The proof node to check
   * @param expected The (optional) formula that is the expected conclusion of
   * the proof node.
   * @return The conclusion of the proof node if successful or null if the
   * proof is malformed, or if no checker is available for id.
   */
  Node check(ProofNode* pn, Node expected = Node::null());
  /** Same as above, with explicit arguments
   *
   * @param id The id of the proof node to check
   * @param children The children of the proof node to check
   * @param args The arguments of the proof node to check
   * @param expected The (optional) formula that is the expected conclusion of
   * the proof node.
   * @return The conclusion of the proof node if successful or null if the
   * proof is malformed, or if no checker is available for id.
   */
  Node check(PfRule id,
             const std::vector<std::shared_ptr<ProofNode>>& children,
             const std::vector<Node>& args,
             Node expected = Node::null());
  /** Indicate that psc is the checker for proof rule id */
  void registerChecker(PfRule id, ProofRuleChecker* psc);

 private:
  /** Maps proof steps to their checker */
  std::map<PfRule, ProofRuleChecker*> d_checker;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_CHECKER_H */
