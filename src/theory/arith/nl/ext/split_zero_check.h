/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for split zero lemma.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__SPLIT_ZERO_CHECK_H
#define CVC5__THEORY__ARITH__NL__EXT__SPLIT_ZERO_CHECK_H

#include "expr/node.h"
#include "context/cdhashset.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

struct ExtState;

class SplitZeroCheck
{
 public:
  SplitZeroCheck(ExtState* data);

  /** check split zero
   *
   * Returns a set of theory lemmas of the form
   *   t = 0 V t != 0
   * where t is a term that exists in the current context.
   */
  void check();

 private:
  using NodeSet = context::CDHashSet<Node>;

  /** Basic data that is shared with other checks */
  ExtState* d_data;
  /** cache of terms t for which we have added the lemma ( t = 0 V t != 0 ). */
  NodeSet d_zero_split;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
