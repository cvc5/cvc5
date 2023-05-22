/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing assertions for an SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__EXPAND_DEFINITIONS_H
#define CVC5__SMT__EXPAND_DEFINITIONS_H

#include <unordered_map>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace smt {

/**
 * Implements expand definitions, which returns the expanded form of a term.
 *
 * This method is similar in nature to PropEngine::preprocess in that it
 * converts a (possibly user-provided) term into the form that we pass
 * internally. However, this method can be seen as a lightweight version
 * of that method which only does enough conversions to make, e.g., get-value
 * accurate on the resulting term. Moreover, this method does not impact
 * the state of lemmas known to the PropEngine.
 *
 * This utility is not proof producing, since it should only be used for
 * getting model values.
 */
class ExpandDefs : protected EnvObj
{
 public:
  ExpandDefs(Env& env);
  ~ExpandDefs();
  /**
   * Expand definitions in term n. Return the expanded form of n.
   *
   * @param n The node to expand
   * @param cache Cache of previous results
   * @return The expanded term.
   */
  Node expandDefinitions(TNode n, std::unordered_map<Node, Node>& cache);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
