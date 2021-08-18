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
 * Relevance manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DIFFICULTY_MANAGER__H
#define CVC5__THEORY__DIFFICULTY_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5 {
  
class Env;

namespace theory {

/**
 */
class DifficultyManager
{
 public:
  DifficultyManager(Env& env);
  /**
   * Notify (preprocessed) assertions. This is called for input formulas or
   * lemmas that need justification that have been fully processed, just before
   * adding them to the PropEngine.
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
  /** Singleton version of above */
  void notifyPreprocessedAssertion(Node n);
  /**
   * Get difficulty map
   */
  void getDifficultyMap(std::map<Node, Node>& dmap);
private:
  /** Reference to env */
  Env& d_env;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__DIFFICULTY_MANAGER__H */
