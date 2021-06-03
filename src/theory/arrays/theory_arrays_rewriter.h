/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/type_enumerator.h"

namespace cvc5 {
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
  /**
   * Puts array constant node into normal form. This is so that array constants
   * that are distinct nodes are semantically disequal.
   */
  static Node normalizeConstant(TNode node);

 public:
  /** Normalize a constant whose index type has cardinality indexCard */
  static Node normalizeConstant(TNode node, Cardinality indexCard);

  RewriteResponse postRewrite(TNode node) override;

  RewriteResponse preRewrite(TNode node) override;

  TrustNode expandDefinition(Node node) override;

  static inline void init() {}
  static inline void shutdown() {}

}; /* class TheoryArraysRewriter */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
