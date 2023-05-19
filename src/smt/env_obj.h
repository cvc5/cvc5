/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The base class for everything that nees access to the environment (Env)
 * instance, which gives access to global utilities available to internal code.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__ENV_OBJ_H
#define CVC5__SMT__ENV_OBJ_H

#include <memory>

#include "expr/node.h"

namespace cvc5::context {
class Context;
class UserContext;
}  // namespace cvc5::context

namespace cvc5::internal {

class Env;
class LogicInfo;
class NodeManager;
class Options;
class StatisticsRegistry;

namespace options {
enum class OutputTag;
}
using OutputTag = options::OutputTag;

class EnvObj
{
 protected:
  /** Constructor. */
  EnvObj(Env& env);
  EnvObj() = delete;
  /** Destructor.  */
  virtual ~EnvObj() {}

  /**
   * Rewrite a node.
   * This is a wrapper around theory::Rewriter::rewrite via Env.
   */
  Node rewrite(TNode node) const;
  /**
   * Extended rewrite a node.
   * This is a wrapper around theory::Rewriter::extendedRewrite via Env.
   */
  Node extendedRewrite(TNode node, bool aggr = true) const;
  /**
   * Evaluate node n under the substitution args -> vals.
   * This is a wrapper about theory::Rewriter::evaluate via Env.
   */
  Node evaluate(TNode n,
                const std::vector<Node>& args,
                const std::vector<Node>& vals,
                bool useRewriter = true) const;
  /** Same as above, with a visited cache. */
  Node evaluate(TNode n,
                const std::vector<Node>& args,
                const std::vector<Node>& vals,
                const std::unordered_map<Node, Node>& visited,
                bool useRewriter = true) const;

  /** Get the options object (const version only) via Env. */
  const Options& options() const;

  /** Get a pointer to the Context via Env. */
  context::Context* context() const;

  /** Get a pointer to the UserContext via Env. */
  context::UserContext* userContext() const;

  /** Get the resource manager owned by this Env. */
  ResourceManager* resourceManager() const;

  /** Get the current logic information. */
  const LogicInfo& logicInfo() const;

  /** Get the statistics registry via Env. */
  StatisticsRegistry& statisticsRegistry() const;

  /** Convenience wrapper for Env::isOutputOn(). */
  bool isOutputOn(OutputTag tag) const;

  /** Convenience wrapper for Env::output(). */
  std::ostream& output(OutputTag tag) const;

  /** Convenience wrapper for Env::isVerboseOn(). */
  bool isVerboseOn(int64_t level) const;

  /** Convenience wrapper for Env::verbose(). */
  std::ostream& verbose(int64_t) const;

  /** Convenience wrapper for Env::verbose(0). */
  std::ostream& warning() const;

  /** The associated environment. */
  Env& d_env;
};

}  // namespace cvc5::internal
#endif
