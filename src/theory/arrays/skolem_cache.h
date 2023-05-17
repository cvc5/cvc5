/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arrays skolem cache.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__SKOLEM_CACHE_H
#define CVC5__THEORY__ARRAYS__SKOLEM_CACHE_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * The arrays skolem cache, which provides static methods for constructing
 * skolems with witness forms.
 */
class SkolemCache
{
 public:
  SkolemCache();
  ~SkolemCache() {}

  /**
   * Get the skolem correspoding to the index that witnesses the disequality
   * deq between arrays a and b. The witness form of this skolem is:
   * (witness ((x T)) (=> (not (= a b)) (not (= (select a x) (select b x)))))
   * This skolem is unique for deq, calling this method will always return the
   * same skolem over the lifetime of deq.
   */
  static Node getExtIndexSkolem(Node deq);

  /**
   * Get the bound variable for given EQ_RANGE operator. This bound variable
   * is unique for `eqr`. Calling this method will always return the same bound
   * variable over the lifetime of `eqr`.
   */
  static Node getEqRangeVar(TNode eqr);
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif
