/*********************                                                        */
/*! \file split_zero_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Check for split zero lemma
 **/

#ifndef CVC4__THEORY__ARITH__NL__EXT__SPLIT_ZERO_CHECK_H
#define CVC4__THEORY__ARITH__NL__EXT__SPLIT_ZERO_CHECK_H

#include "expr/node.h"
#include "theory/arith/nl/ext/ext_state.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class SplitZeroCheck
{
 public:
  SplitZeroCheck(ExtState* data, context::Context* ctx);

  /** check split zero
   *
   * Returns a set of theory lemmas of the form
   *   t = 0 V t != 0
   * where t is a term that exists in the current context.
   */
  void check();

 private:
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

  /** Basic data that is shared with other checks */
  ExtState* d_data;
  /** cache of terms t for which we have added the lemma ( t = 0 V t != 0 ). */
  NodeSet d_zero_split;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
