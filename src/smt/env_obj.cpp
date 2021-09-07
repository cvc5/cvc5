/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

EnvObj::EnvObj(Env& env) : d_env(env) {}

Node EnvObj::rewrite(TNode node) { return d_env.getRewriter()->rewrite(node); }

Node EnvObj::extendedRewrite(TNode node, bool aggr)
{
  return d_env.getRewriter()->extendedRewrite(node, aggr);
}

const LogicInfo& EnvObj::logicInfo() const { return d_env.getLogicInfo(); }

const Options& EnvObj::options() const { return d_env.getOptions(); }

context::Context* EnvObj::context() const { return d_env.getContext(); }

context::UserContext* EnvObj::userContext() const
{
  return d_env.getUserContext();
}

}  // namespace cvc5
