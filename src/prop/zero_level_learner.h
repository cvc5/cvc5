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
 * Learner for literals asserted at level zero.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__ZERO_LEVEL_LEARNER_H
#define CVC5__PROP__ZERO_LEVEL_LEARNER_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5 {
namespace prop {

class PropEngine;

/**
 * The module for processing literals that are learned at decision level zero.
 *
 * This tracks the literals that are asserted at decision level zero. It
 * computes which literals are "learnable", which currently is limited to those
 * that are over atoms that appear in the input assertions.
 *
 * The module can be queried for the set of learned literals, and also is
 * responsible for printing the literals it learns.
 */
class ZeroLevelLearner : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  ZeroLevelLearner(Env& env, PropEngine* propEngine);

  ~ZeroLevelLearner();

  void notifyInputFormulas(const std::vector<Node>& assertions,
                           std::unordered_map<size_t, Node>& skolemMap,
                           const std::vector<Node>& ppl);
  /**
   * Notify the given literal was asserted
   */
  void notifyAsserted(TNode assertion);

  /** Get the zero-level assertions */
  std::vector<Node> getLearnedZeroLevelLiterals() const;

 private:
  static void getAtoms(TNode a,
                       std::unordered_set<TNode>& visited,
                       NodeSet& ppLits);

  /** The prop engine we are using. */
  PropEngine* d_propEngine;

  /** Set of literals that hold at level 0 */
  NodeSet d_levelZeroAsserts;

  /** Set of learnable literals that hold at level 0 */
  NodeSet d_levelZeroAssertsLearned;

  /** Whether we have seen an assertion level > 0 */
  context::CDO<bool> d_nonZeroAssert;

  /** Preprocessed literals that are not learned */
  NodeSet d_ppnAtoms;

  /** Already learned TEMPORARY */
  NodeSet d_pplAtoms;

  /** Current counter of assertions */
  size_t d_assertNoLearnCount;
}; /* class ZeroLevelLearner */

}  // namespace prop
}  // namespace cvc5

#endif
