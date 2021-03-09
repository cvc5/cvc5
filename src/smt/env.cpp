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
#include "smt/dump.h"
#include "smt/dump_manager.h"
#include "smt/smt_engine_stats.h"
#include "theory/rewriter.h"
#include "util/resource_manager.h"

using namespace CVC4::smt;

namespace CVC4 {

Env::Env(NodeManager* nm, Options* optr)
    : d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_nodeManager(nm),
      d_pnm(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_dumpm(new DumpManager(d_userContext.get())),
      d_logic(),
      d_statisticsRegistry(nullptr),
      d_resourceManager(nullptr)
{
  if (optr != nullptr)
  {
    // if we provided a set of options, copy their values to the options
    // owned by this Env.
    d_options.copyValues(*optr);
  }
  d_statisticsRegistry.reset(new StatisticsRegistry());
  d_resourceManager.reset(
      new ResourceManager(*d_statisticsRegistry.get(), d_options));
}

Env::~Env() {}

context::UserContext* Env::getUserContext() { return d_userContext.get(); }

context::Context* Env::getContext() { return d_context.get(); }

NodeManager* Env::getNodeManager() const { return d_nodeManager; }

ProofNodeManager* Env::getProofNodeManager() { return d_pnm; }

theory::Rewriter* Env::getRewriter() { return d_rewriter.get(); }

DumpManager* Env::getDumpManager() { return d_dumpm.get(); }

const LogicInfo& Env::getLogicInfo() const { return d_logic; }

StatisticsRegistry* Env::getStatisticsRegistry()
{
  return d_statisticsRegistry.get();
}

const Options& Env::getOptions() const { return d_options; }

ResourceManager* Env::getResourceManager() { return d_resourceManager.get(); }

const Printer& Env::getPrinter()
{
  return *Printer::getPrinter(d_options[options::outputLanguage]);
}

std::ostream& Env::getDumpOut() { return *d_options.getOut(); }

}  // namespace CVC4
