/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
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

#ifndef CVC5__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H
#define CVC5__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H

#include <unordered_map>
#include <unordered_set>

#include "theory/rewriter.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {

class Env;
class TConvProofGenerator;

namespace theory {

namespace arrays {

Node getMostFrequentValue(TNode store);
uint64_t getMostFrequentValueCount(TNode store);
void setMostFrequentValue(TNode store, TNode value);
void setMostFrequentValueCount(TNode store, uint64_t count);

class TheoryArraysRewriter : public TheoryRewriter
{
 public:
  TheoryArraysRewriter(NodeManager* nm, Rewriter* r);

  /** Normalize a constant whose index type has cardinality indexCard */
  static Node normalizeConstant(NodeManager* nm,
                                TNode node,
                                Cardinality indexCard);

  /* Expands the eqrange predicate (eqrange a b i j) to the quantified formula
   * (forall ((x T))
   *  (=> (and (<= i x) (<= x j)) (= (select a x) (select b x)))).
   */
  static Node expandEqRange(NodeManager* nm, TNode node);

  RewriteResponse postRewrite(TNode node) override;

  RewriteResponse preRewrite(TNode node) override;

  /**
   * Rewrite n based on the proof rewrite rule id.
   * @param id The rewrite rule.
   * @param n The node to rewrite.
   * @return The rewritten version of n based on id, or Node::null() if n
   * cannot be rewritten.
   */
  Node rewriteViaRule(ProofRewriteRule id, const Node& n) override;

  Node expandDefinition(Node node) override;

  /**
   * Puts array constant node into normal form. This is so that array constants
   * that are distinct nodes are semantically disequal.
   *
   * This method should only be called on STORE chains whose AST is built
   * from constant terms only.
   */
  static Node normalizeConstant(NodeManager* nm, TNode node);

  /**
   * @param n The term to rewrite, expected to be a store or select whose
   * index can be "pushed" beneath indices on the first argument.
   * @param pg If provided, stores a set of small step rewrites that suffice
   * to show that n rewrites to the returned term.
   * @return the result of rewriting n.
   */
  Node computeNormalizeOp(const Node& n,
                          TConvProofGenerator* pg = nullptr) const;

 private:
  /**
   * Pointer to the rewriter. NOTE this is a cyclic dependency, and should
   * be removed.
   */
  Rewriter* d_rewriter;
  /**
   * Make rewritten equality.
   * @param a The first term.
   * @param b The second term.
   * @return the rewritten form of the equality between a and b.
   */
  Node mkEqNode(const Node& a, const Node& b) const;
}; /* class TheoryArraysRewriter */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
