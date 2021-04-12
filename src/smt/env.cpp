/*********************                                                        */
/*! \file env.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Smt Environment, main access to global utilities available to
 ** internal code.
 **/

#include "smt/env.h"

#include "context/context.h"
#include "expr/node.h"
#include "expr/term_conversion_proof_generator.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "smt/dump_manager.h"
#include "smt/smt_engine_stats.h"
#include "theory/rewriter.h"
#include "util/resource_manager.h"

using namespace cvc5::smt;

namespace cvc5 {

Env::Env(NodeManager* nm)
    : d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_nodeManager(nm),
      d_proofNodeManager(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_dumpManager(new DumpManager(d_userContext.get())),
      d_logic(),
      d_statisticsRegistry(std::make_unique<StatisticsRegistry>()),
      d_resourceManager(std::make_unique<ResourceManager>(*d_statisticsRegistry, d_options))
{
}

Env::~Env() {}

void Env::setOptions(Options* optr)
{
  if (optr != nullptr)
  {
    // if we provided a set of options, copy their values to the options
    // owned by this Env.
    d_options.copyValues(*optr);
  }
}

void Env::setProofNodeManager(ProofNodeManager* pnm)
{
  d_proofNodeManager = pnm;
  d_rewriter->setProofNodeManager(pnm);
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
