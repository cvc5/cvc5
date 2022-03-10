/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The care argument callback.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__CARE_ARGUMENT_CALLBACK_H
#define CVC5__THEORY__CARE_ARGUMENT_CALLBACK_H

#include "expr/node_trie_algorithm.h"
#include "theory/theory.h"

namespace cvc5 {
namespace theory {

/**
 * The standard callback for computing the care pairs from a node trie.
 */
class CarePairArgumentCallback : public NodeTriePathCompareCallback
{
  public:
  CarePairArgumentCallback(Theory& t) : d_theory(t) {}
  ~CarePairArgumentCallback() {}
  /** Whether to consider a pair in paths in a trie */
  bool considerPath(TNode a, TNode b) override;
  /** Process leaves */
  void processData(TNode fa, TNode fb) override;
  private:
  /** Reference to theory */
  Theory& d_theory;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__CARE_ARGUMENT_CALLBACK_H */
