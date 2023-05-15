/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

class EagerProofGenerator;
class Env;

namespace theory {

namespace arrays {

Node getMostFrequentValue(TNode store);
uint64_t getMostFrequentValueCount(TNode store);
void setMostFrequentValue(TNode store, TNode value);
void setMostFrequentValueCount(TNode store, uint64_t count);

static inline Node mkEqNode(Node a, Node b) {
  return a.eqNode(b);
}

class TheoryArraysRewriter : public TheoryRewriter
{
 public:
  TheoryArraysRewriter(Env& env);

  /** Normalize a constant whose index type has cardinality indexCard */
  static Node normalizeConstant(TNode node, Cardinality indexCard);

  /* Expands the eqrange predicate (eqrange a b i j) to the quantified formula
   * (forall ((x T))
   *  (=> (and (<= i x) (<= x j)) (= (select a x) (select b x)))).
   */
  static Node expandEqRange(TNode node);

  RewriteResponse postRewrite(TNode node) override;

  RewriteResponse preRewrite(TNode node) override;

  TrustNode expandDefinition(Node node) override;

  static inline void init() {}

  /**
   * Puts array constant node into normal form. This is so that array constants
   * that are distinct nodes are semantically disequal.
   *
   * This method should only be called on STORE chains whose AST is built
   * from constant terms only.
   */
  static Node normalizeConstant(TNode node);

 private:
  /** The associated rewriter. */
  Rewriter* d_rewriter;

  std::unique_ptr<EagerProofGenerator> d_epg;
}; /* class TheoryArraysRewriter */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
