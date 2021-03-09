/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include "smt/smt_engine.h"

#include "api/cvc4cpp.h"
#include "base/check.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "decision/decision_engine.h"
#include "expr/bound_var_manager.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "printer/printer.h"
#include "proof/proof_manager.h"
#include "proof/unsat_core.h"
#include "prop/prop_engine.h"
#include "smt/abduction_solver.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/check_models.h"
#include "smt/defined_function.h"
#include "smt/dump.h"
#include "smt/dump_manager.h"
#include "smt/interpolation_solver.h"
#include "smt/listeners.h"
#include "smt/logic_exception.h"
#include "smt/model_blocker.h"
#include "smt/model_core_builder.h"
#include "smt/node_command.h"
#include "smt/options_manager.h"
#include "smt/preprocessor.h"
#include "smt/proof_manager.h"
#include "smt/quant_elim_solver.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_engine_state.h"
#include "smt/smt_engine_stats.h"
#include "smt/smt_solver.h"
#include "smt/sygus_solver.h"
#include "smt/unsat_core_manager.h"
#include "theory/quantifiers/instantiation_list.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"
#include "util/random.h"
#include "util/resource_manager.h"

// required for hacks related to old proofs for unsat cores
#include "base/configuration.h"
#include "base/configuration_private.h"

using namespace std;
using namespace CVC4::smt;
using namespace CVC4::preprocessing;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

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
