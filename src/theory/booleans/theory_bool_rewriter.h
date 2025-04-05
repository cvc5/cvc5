/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H
#define CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {

class TConvProofGenerator;
class CDProof;

namespace theory {
namespace booleans {

class TheoryBoolRewriter : public TheoryRewriter
{
 public:
  TheoryBoolRewriter(NodeManager* nm);
  RewriteResponse preRewrite(TNode node) override;
  RewriteResponse postRewrite(TNode node) override;

  /**
   * Rewrite n based on the proof rewrite rule id.
   * @param id The rewrite rule.
   * @param n The node to rewrite.
   * @return The rewritten version of n based on id, or Node::null() if n
   * cannot be rewritten.
   */
  Node rewriteViaRule(ProofRewriteRule id, const Node& n) override;
  /**
   * Eliminates IMPLIES/XOR, removes duplicates/infers tautologies of AND/OR,
   * and computes NNF.
   *
   * @param nm Pointer to node manager.
   * @param n The node to rewrite.
   * @param pg If non-null, this stores rewrite rules that are capable of
   * proving that n is equal to its normalized form. This conversion generator
   * is expected to use a BoolSkeletonTermContext (see expr/term_context.h) as
   * this method only traverses the propositional skeleton of n.
   * @return The normalized form of n.
   */
  static Node computeNnfNorm(NodeManager* nm,
                             const Node& n,
                             TConvProofGenerator* pg = nullptr);

  /**
   * Get BV invert solve, given input t1 = t2 and variable x, returns the solved
   * form r for x, where x = r is equivalent to t1 = t2.
   *
   * @param nm Pointer to node manager.
   * @param lit The node to rewrite.
   * @param var The variable to solve for.
   * @param disallowedKinds The set of kinds we are not allowed to traverse on
   * the path to var.
   * @param cdp If provided, we add a proof of (= lit ret) to cdp, where ret is
   * the equality returned by this method.
   * @return The right hand side r corresponding to the solved form for var in
   * lit, or null if we fail.
   */
  static Node getBvInvertSolve(NodeManager* nm,
                               const Node& lit,
                               const Node& var,
                               std::unordered_set<Kind>& disallowedKinds,
                               CDProof* cdp = nullptr);

 protected:
  /**
   * Helper method for computeNnfNorm.
   */
  static bool addNnfNormChild(std::vector<Node>& children,
                              Node c,
                              Kind k,
                              std::map<Node, bool>& lit_pol,
                              bool& childrenChanged);
  /**
   * Helper method which performs flattening.
   *
   * @param n The node to flatten
   * @param trivialNode The trivial node, e.g. false if n is an AND application
   * @param skipNode The skip node, e.g. true if n is an AND application
   * @return The flattened node.
   */
  RewriteResponse flattenNode(TNode n, TNode trivialNode, TNode skipNode);
  /**
   * Helper method for making a negation
   *
   * @param n The node to negate
   * @return The negation of n.
   */
  Node makeNegation(TNode n);
  /** Common constants */
  Node d_true;
  Node d_false;
};

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H */
