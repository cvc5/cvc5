/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Smt Environment, main access to global utilities available to
 * internal code.
 */

#include "smt/env.h"

#include "context/context.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "proof/conv_proof_generator.h"
#include "smt/dump_manager.h"
#include "smt/smt_engine_stats.h"
#include "theory/rewriter.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

using namespace cvc5::smt;

namespace cvc5 {

Env::Env(NodeManager* nm, Options* opts)
    : d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_nodeManager(nm),
      d_proofNodeManager(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_topLevelSubs(new theory::TrustSubstitutionMap(d_userContext.get())),
      d_dumpManager(new DumpManager(d_userContext.get())),
      d_logic(),
      d_statisticsRegistry(std::make_unique<StatisticsRegistry>()),
      d_options(),
      d_resourceManager()
{
  if (opts != nullptr)
  {
    d_options.copyValues(*opts);
  }
  d_resourceManager = std::make_unique<ResourceManager>(*d_statisticsRegistry, d_options);
}

Env::~Env() {}

void Env::setProofNodeManager(ProofNodeManager* pnm)
{
  Assert(pnm != nullptr);
  Assert(d_proofNodeManager == nullptr);
  d_proofNodeManager = pnm;
  d_rewriter->setProofNodeManager(pnm);
  d_topLevelSubs->setProofNodeManager(pnm);
}

void Env::shutdown()
{
  d_rewriter.reset(nullptr);
  d_dumpManager.reset(nullptr);
  // d_resourceManager must be destroyed before d_statisticsRegistry
  d_resourceManager.reset(nullptr);
}

context::UserContext* Env::getUserContext() { return d_userContext.get(); }

context::Context* Env::getContext() { return d_context.get(); }

NodeManager* Env::getNodeManager() const { return d_nodeManager; }

ProofNodeManager* Env::getProofNodeManager() { return d_proofNodeManager; }

theory::Rewriter* Env::getRewriter() { return d_rewriter.get(); }

theory::TrustSubstitutionMap& Env::getTopLevelSubstitutions()
{
  return *d_topLevelSubs.get();
}

DumpManager* Env::getDumpManager() { return d_dumpManager.get(); }

const LogicInfo& Env::getLogicInfo() const { return d_logic; }

StatisticsRegistry& Env::getStatisticsRegistry()
{
  return *d_statisticsRegistry;
}

const Options& Env::getOptions() const { return d_options; }

ResourceManager* Env::getResourceManager() const
{
  return d_resourceManager.get();
}

const Printer& Env::getPrinter()
{
  return *Printer::getPrinter(d_options[options::outputLanguage]);
}

std::ostream& Env::getDumpOut() { return *d_options.getOut(); }

}  // namespace cvc5
