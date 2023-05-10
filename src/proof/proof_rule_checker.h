/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof rule checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_RULE_CHECKER_H
#define CVC5__PROOF__PROOF_RULE_CHECKER_H

#include <vector>

#include "expr/node.h"
#include "proof/proof_rule.h"

namespace cvc5::internal {

class ProofChecker;
class ProofNode;

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
   * Note that the input/output of this method expects to be terms in *Skolem
   * form*, which is passed to checkInternal below. Rule checkers may
   * convert premises to witness form when necessary.
   *
   * @param id The id of the proof node to check
   * @param children The premises of the proof node to check. These are nodes
   * corresponding to the conclusion (ProofNode::getResult) of the children
   * of the proof node we are checking in Skolem form.
   * @param args The arguments of the proof node to check
   * @return The conclusion of the proof node, in Skolem form, if successful or
   * null if such a proof node is malformed.
   */
  Node check(PfRule id,
             const std::vector<Node>& children,
             const std::vector<Node>& args);

  /** get an index from a node, return false if we fail */
  static bool getUInt32(TNode n, uint32_t& i);
  /** get a Boolean from a node, return false if we fail */
  static bool getBool(TNode n, bool& b);
  /** get a Kind from a node, return false if we fail */
  static bool getKind(TNode n, Kind& k);
  /** Make a Kind into a node */
  static Node mkKindNode(Kind k);

  /** Register all rules owned by this rule checker into pc. */
  virtual void registerTo(ProofChecker* pc) {}

 protected:
  /**
   * This checks a single step in a proof.
   *
   * @param id The id of the proof node to check
   * @param children The premises of the proof node to check. These are nodes
   * corresponding to the conclusion (ProofNode::getResult) of the children
   * of the proof node we are checking.
   * @param args The arguments of the proof node to check
   * @return The conclusion of the proof node if successful or null if such a
   * proof node is malformed.
   */
  virtual Node checkInternal(PfRule id,
                             const std::vector<Node>& children,
                             const std::vector<Node>& args) = 0;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_RULE_CHECKER_H */
