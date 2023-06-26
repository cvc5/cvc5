/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof node manager utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_NODE_MANAGER_H
#define CVC5__PROOF__PROOF_NODE_MANAGER_H

#include <vector>

#include "expr/node.h"
#include "proof/proof_rule.h"

namespace cvc5::internal {

class ProofChecker;
class ProofNode;
class Options;

namespace theory {
class Rewriter;
}

/**
 * A manager for proof node objects. This is a trusted interface for creating
 * and updating ProofNode objects.
 *
 * In more detail, we say a ProofNode is "well-formed (with respect to checker
 * X)" if its d_proven field is non-null, and corresponds to the formula that
 * the ProofNode proves according to X. The ProofNodeManager class constructs
 * and update nodes that are well-formed with respect to its underlying checker.
 *
 * If no checker is provided, then the ProofNodeManager assigns the d_proven
 * field of ProofNode based on the provided "expected" argument in mkNode below,
 * which must be provided in this case.
 *
 * The ProofNodeManager is used as a trusted way of updating ProofNode objects
 * via updateNode below. In particular, this method leaves the d_proven field
 * unchanged and updates (if possible) the remaining content of a given proof
 * node.
 *
 * Notice that ProofNode objects are mutable, and hence this class does not
 * cache the results of mkNode. A version of this class that caches
 * immutable version of ProofNode objects could be built as an extension
 * or layer on top of this class.
 */
class ProofNodeManager
{
 public:
  ProofNodeManager(const Options& opts,
                   theory::Rewriter* rr,
                   ProofChecker* pc = nullptr);
  ~ProofNodeManager() {}
  /**
   * This constructs a ProofNode with the given arguments. The expected
   * argument, when provided, indicates the formula that the returned node
   * is expected to prove. If we find that it does not, based on the underlying
   * checker, this method returns nullptr.
   *
   * @param id The id of the proof node.
   * @param children The children of the proof node.
   * @param args The arguments of the proof node.
   * @param expected (Optional) the expected conclusion of the proof node.
   * @return the proof node, or nullptr if the given arguments do not
   * consistute a proof of the expected conclusion according to the underlying
   * checker, if both are provided. It also returns nullptr if neither the
   * checker nor the expected field is provided, since in this case the
   * conclusion is unknown.
   */
  std::shared_ptr<ProofNode> mkNode(
      PfRule id,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args,
      Node expected = Node::null());
  /**
   * Make the proof node corresponding to the assumption of fact.
   *
   * @param fact The fact to assume.
   * @return The ASSUME proof of fact.
   */
  std::shared_ptr<ProofNode> mkAssume(Node fact);
  /**
   * Make symm, which accounts for whether the child is already a SYMM
   * node, in which case we return its child.
   */
  std::shared_ptr<ProofNode> mkSymm(std::shared_ptr<ProofNode> child,
                                    Node expected = Node::null());
  /**
   * Make transitivity proof, where children contains one or more proofs of
   * equalities that form an ordered chain. In other words, the vector children
   * is a legal set of children for an application of TRANS.
   */
  std::shared_ptr<ProofNode> mkTrans(
      const std::vector<std::shared_ptr<ProofNode>>& children,
      Node expected = Node::null());

  /**
   * Make scope having body pf and arguments (assumptions-to-close) assumps.
   * If ensureClosed is true, then this method throws an assertion failure if
   * the returned proof is not closed. This is the case if a free assumption
   * of pf is missing from the vector assumps.
   *
   * For conveinence, the proof pf may be modified to ensure that the overall
   * result is closed. For instance, given input:
   *   pf = TRANS( ASSUME( x=y ), ASSUME( y=z ) )
   *   assumps = { y=x, y=z }
   * This method will modify pf to be:
   *   pf = TRANS( SYMM( ASSUME( y=x ) ), ASSUME( y=z ) )
   * so that y=x matches the free assumption. The returned proof is:
   *   SCOPE(TRANS( SYMM( ASSUME( y=x ) ), ASSUME( y=z ) ) :args { y=x, y=z })
   *
   * When ensureClosed is true, duplicates are eliminated from assumps. The
   * reason for this is due to performance, since in this method, assumps is
   * converted to an unordered_set to do the above check and hence it is a
   * convienient time to eliminate duplicate literals.
   *
   * Additionally, if both ensureClosed and doMinimize are true, assumps is
   * updated to contain exactly the free asumptions of pf. This also includes
   * having no duplicates. Furthermore, if assumps is empty after minimization,
   * this method is a no-op.
   *
   * In each case, the update vector assumps is passed as arguments to SCOPE.
   *
   * @param pf The body of the proof,
   * @param assumps The assumptions-to-close of the scope,
   * @param ensureClosed Whether to ensure that the proof is closed,
   * @param doMinimize Whether to minimize assumptions.
   * @param expected the node that the scope should prove.
   * @return The scoped proof.
   */
  std::shared_ptr<ProofNode> mkScope(std::shared_ptr<ProofNode> pf,
                                     std::vector<Node>& assumps,
                                     bool ensureClosed = true,
                                     bool doMinimize = false,
                                     Node expected = Node::null());
  /**
   * This method updates pn to be a proof of the form <id>( children, args ),
   * while maintaining its d_proven field. This method returns false if this
   * proof manager is using a checker, and we compute that the above proof
   * is not a proof of the fact that pn previously proved.
   *
   * @param pn The proof node to update.
   * @param id The updated id of the proof node.
   * @param children The updated children of the proof node.
   * @param args The updated arguments of the proof node.
   * @return true if the update was successful.
   *
   * Notice that updateNode always returns true if there is no underlying
   * checker.
   */
  bool updateNode(ProofNode* pn,
                  PfRule id,
                  const std::vector<std::shared_ptr<ProofNode>>& children,
                  const std::vector<Node>& args);
  /**
   * Update node pn to have the contents of pnr. It should be the case that
   * pn and pnr prove the same fact, otherwise false is returned and pn is
   * unchanged.
   */
  bool updateNode(ProofNode* pn, ProofNode* pnr);
  /**
   * Ensure that pn is checked, regardless of the proof check format.
   */
  void ensureChecked(ProofNode* pn);
  /** Get the underlying proof checker */
  ProofChecker* getChecker() const;
  /**
   * Cancel double SYMM. Returns a proof node that is not a double application
   * of SYMM, e.g. for (SYMM (SYMM (r P))), this returns (r P) where r != SYMM.
   */
  static ProofNode* cancelDoubleSymm(ProofNode* pn);

 private:
  /** Reference to the options */
  const Options& d_opts;
  /** The rewriter */
  theory::Rewriter* d_rewriter;
  /** The (optional) proof checker */
  ProofChecker* d_checker;
  /** the true node */
  Node d_true;
  /** Check internal
   *
   * This returns the result of proof checking a ProofNode with the provided
   * arguments with an expected conclusion, which may not null if there is
   * no expected conclusion.
   *
   * This throws an assertion error if we fail to check such a proof node, or
   * if expected is provided (non-null) and is different what is proven by the
   * other arguments.
   *
   * The flag didCheck is set to true if the underlying proof checker was
   * invoked. This may be false if e.g. the proof checking mode is lazy.
   */
  Node checkInternal(PfRule id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args,
                     Node expected,
                     bool& didCheck);
  /**
   * Update node internal, return true if successful. This is called by
   * the update node methods above. The argument needsCheck is whether we
   * need to check the correctness of the rule application. This is false
   * for the updateNode routine where pnr is an (already checked) proof node.
   */
  bool updateNodeInternal(
      ProofNode* pn,
      PfRule id,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args,
      bool needsCheck);
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_NODE_H */
