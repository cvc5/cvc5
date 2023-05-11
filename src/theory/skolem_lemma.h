/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The skolem lemma utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SKOLEM_LEMMA_H
#define CVC5__THEORY__SKOLEM_LEMMA_H

#include "expr/node.h"
#include "proof/trust_node.h"

namespace cvc5::internal {
namespace theory {

/**
 * A skolem lemma is a pair containing a trust node repreresenting a lemma
 * and the skolem it is for. A common example would be the trust node proving
 * the lemma:
 *    (ite C (= k A) (= k B))
 * and the skolem k.
 *
 * Skolem lemmas can be used as a way of tracking the relevance of a lemma.
 * They can be used for things like term formula removal and preprocessing.
 */
class SkolemLemma
{
 public:
  /**
   * Make skolem from trust node lem of kind LEMMA and skolem k.
   */
  SkolemLemma(TrustNode lem, Node k);

  /** The lemma, a trust node of kind LEMMA */
  TrustNode d_lemma;
  /** The skolem associated with that lemma */
  Node d_skolem;

  /** Get proven from the lemma */
  Node getProven() const;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SKOLEM_LEMMA_H */
