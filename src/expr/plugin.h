/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Plugin class, which is communicated to via TheoryEngine and PropEngine
 * when theory lemmas and SAT clauses are learned, and can be used to
 * inject new lemmas during check.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__PLUGIN_H
#define CVC5__EXPR__PLUGIN_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * A plugin. This is the internal interface for a user-provided plugin. The
 * class PluginInternal in api/cvc5.cpp inherits from this class. It is used
 * to convert to/from callbacks from the API. It is used by the PluginModule
 * for implementing a theory engine module, which is called during solving
 * by TheoryEngine, and by PropEngine when SAT clauses are learned.
 */
class Plugin
{
 public:
  /** Construct a plugin. */
  Plugin(NodeManager* nm);
  virtual ~Plugin();
  /**
   * Check function.
   * @return a vector of lemmas to add to the SAT solver.
   */
  virtual std::vector<Node> check() = 0;
  /**
   * Notify SAT clause, called when lem is learned by the SAT solver.
   *
   * @param lem The lemma learned by the SAT solver.
   */
  virtual void notifySatClause(const Node& lem) = 0;
  /**
   * Notify theory lemma, called when lem is added a theory lemma to the SAT
   * solver.
   *
   * @param lem The theory lemma given to the SAT solver.
   */
  virtual void notifyTheoryLemma(const Node& lem) = 0;
  /**
   * Get name of this plugin, for debugging.
   * @return the name of the plugin.
   */
  virtual std::string getName() = 0;

 private:
  /** Pointer to node manager */
  NodeManager* d_nm;
};

}  // namespace cvc5::internal

#endif /*CVC5__EXPR__PLUGIN_H*/
