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
 * Plugin
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
 * to convert to/from callbacks from the API.
 */
class Plugin
{
 public:
  /** Construct a plugin. */
  Plugin() {}
  virtual ~Plugin() {}
  /**
   * Check function, returns a vector of lemmas to add to the SAT solver.
   */
  virtual std::vector<Node> check() = 0;
  /**
   * Notify SAT clause, called when lem is learned by the SAT solver.
   */
  virtual void notifySatClause(const Node& lem) = 0;
  /**
   * Notify theory lemma, called when lem is added a theory lemma to the SAT
   * solver.
   */
  virtual void notifyTheoryLemma(const Node& lem) = 0;
  /** Get name of this plugin, for debugging. */
  virtual std::string getName() = 0;
  /**
   * Get sharable formula. This returns an equivalent version of the given
   * lemma n that can be shared externally. In particular, we require that the
   * returned formula does not have any internally generated symbols, i.e.
   * skolems. If n cannot be converted to a suitable formula, we return the
   * null node.
   */
  static Node getSharableFormula(const Node& n);
};

}  // namespace cvc5::internal

#endif /*CVC5__EXPR__ORACLE_H*/
