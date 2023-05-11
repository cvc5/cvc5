/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
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

#include "smt/env_obj.h"

#include "options/options.h"
#include "smt/env.h"
#include "theory/rewriter.h"

namespace cvc5::internal {

EnvObj::EnvObj(Env& env) : d_env(env) {}

Node EnvObj::rewrite(TNode node) const
{
  return d_env.getRewriter()->rewrite(node);
}

Node EnvObj::extendedRewrite(TNode node, bool aggr) const
{
  return d_env.getRewriter()->extendedRewrite(node, aggr);
}
Node EnvObj::evaluate(TNode n,
                      const std::vector<Node>& args,
                      const std::vector<Node>& vals,
                      bool useRewriter) const
{
  return d_env.evaluate(n, args, vals, useRewriter);
}
Node EnvObj::evaluate(TNode n,
                      const std::vector<Node>& args,
                      const std::vector<Node>& vals,
                      const std::unordered_map<Node, Node>& visited,
                      bool useRewriter) const
{
  return d_env.evaluate(n, args, vals, visited, useRewriter);
}

const Options& EnvObj::options() const { return d_env.getOptions(); }

context::Context* EnvObj::context() const { return d_env.getContext(); }

context::UserContext* EnvObj::userContext() const
{
  return d_env.getUserContext();
}

const LogicInfo& EnvObj::logicInfo() const { return d_env.getLogicInfo(); }

ResourceManager* EnvObj::resourceManager() const
{
  return d_env.getResourceManager();
}

StatisticsRegistry& EnvObj::statisticsRegistry() const
{
  return d_env.getStatisticsRegistry();
}

bool EnvObj::isOutputOn(OutputTag tag) const { return d_env.isOutputOn(tag); }

std::ostream& EnvObj::output(OutputTag tag) const { return d_env.output(tag); }

bool EnvObj::isVerboseOn(int64_t level) const
{
  return d_env.isVerboseOn(level);
}

std::ostream& EnvObj::verbose(int64_t level) const
{
  return d_env.verbose(level);
}

std::ostream& EnvObj::warning() const { return verbose(0); }

}  // namespace cvc5::internal
