/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The care pair argument callback.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__CARE_PAIR_ARGUMENT_CALLBACK_H
#define CVC5__THEORY__CARE_PAIR_ARGUMENT_CALLBACK_H

#include "expr/node_trie_algorithm.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

/**
 * The standard callback for computing the care pairs from a node trie.
 */
class CarePairArgumentCallback : public NodeTriePathPairProcessCallback
{
 public:
  CarePairArgumentCallback(Theory& t);
  ~CarePairArgumentCallback() {}
  /**
   * Call on the arguments a and b of two function applications we are
   * computing care pairs for. Returns true if a and b are not already
   * disequal according to theory combination (Theory::areCareDisequal).
   */
  bool considerPath(TNode a, TNode b) override;
  /**
   * Called when we have two function applications that do not have pairs
   * of disequal arguments at any position. We call Theory::processCarePairArgs
   * to add all relevant care pairs.
   */
  void processData(TNode fa, TNode fb) override;

 private:
  /** Reference to theory */
  Theory& d_theory;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__CARE_ARGUMENT_CALLBACK_H */
