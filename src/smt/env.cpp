/*********************                                                        */
/*! \file env.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
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

#include "expr/node.h"
#include "options/printer_options.h"
#include "printer/printer.h"
#include "smt/dump.h"
#include "smt/dump_manager.h"
#include "smt/smt_engine_stats.h"
#include "theory/rewriter.h"
#include "util/resource_manager.h"

using namespace CVC4::smt;

namespace CVC4 {

Env::Env(NodeManager* nm, Options* optr)
    : 
      d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_nodeManager(nm),
      d_pnm(nullptr),
      d_dumpm(new DumpManager(d_userContext.get())),
      d_rewriter(new theory::Rewriter()),
      d_logic(),
      d_statisticsRegistry(nullptr),
      d_outMgr(this),
      d_resourceManager(nullptr),
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

Env::~Env()
{
}

context::UserContext* Env::getUserContext()
{
  return d_userContext.get();
}
context::Context* Env::getContext() { return d_context.get(); }


void Env::finishInit()
{
  // dump out a set-logic command only when raw-benchmark is disabled to avoid
  // dumping the command twice.
  if (Dump.isOn("benchmark") && !Dump.isOn("raw-benchmark"))
  {
      LogicInfo everything;
      everything.lock();
      d_outMgr.getPrinter().toStreamCmdComment(
          d_outMgr.getDumpOut(),
          "CVC4 always dumps the most general, all-supported logic (below), as "
          "some internals might require the use of a logic more general than "
          "the input.");
      d_outMgr.getPrinter().toStreamCmdSetBenchmarkLogic(
          d_outMgr.getDumpOut(), everything.getLogicString());
  }

  // initialize the dump manager
  d_dumpm->finishInit();
}

const LogicInfo& Env::getLogicInfo() const { return d_logic; }

LogicInfo Env::getUserLogicInfo() const
{
  // Lock the logic to make sure that this logic can be queried. We create a
  // copy of the user logic here to keep this method const.
  LogicInfo res = d_userLogic;
  res.lock();
  return res;
}

void Env::setResourceLimit(unsigned long units, bool cumulative) {
  d_resourceManager->setResourceLimit(units, cumulative);
}
void Env::setTimeLimit(unsigned long milis)
{
  d_resourceManager->setTimeLimit(milis);
}

unsigned long Env::getResourceUsage() const {
  return d_resourceManager->getResourceUsage();
}

unsigned long Env::getTimeUsage() const {
  return d_resourceManager->getTimeUsage();
}

unsigned long Env::getResourceRemaining() const
{
  return d_resourceManager->getResourceRemaining();
}

NodeManager* Env::getNodeManager() const { return d_nodeManager; }

Statistics Env::getStatistics() const
{
  return Statistics(*d_statisticsRegistry);
}

SExpr Env::getStatistic(std::string name) const
{
  return d_statisticsRegistry->getStatistic(name);
}

void Env::flushStatistics(std::ostream& out) const
{
  d_nodeManager->getStatisticsRegistry()->flushInformation(out);
  d_statisticsRegistry->flushInformation(out);
}

void Env::safeFlushStatistics(int fd) const
{
  d_nodeManager->getStatisticsRegistry()->safeFlushInformation(fd);
  d_statisticsRegistry->safeFlushInformation(fd);
}

const Options& Env::getOptions() const { return d_options; }

ResourceManager* Env::getResourceManager()
{
  return d_resourceManager.get();
}

DumpManager* Env::getDumpManager() { return d_dumpm.get(); }

const Printer* Env::getPrinter() const
{
  return Printer::getPrinter(d_options[options::outputLanguage]);
}

OutputManager& Env::getOutputManager() { return d_outMgr; }

}/* CVC4 namespace */
