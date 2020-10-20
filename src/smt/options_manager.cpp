/*********************                                                        */
/*! \file options_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Module for managing options of an SmtEngine.
 **/

#include "smt/options_manager.h"

#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/smt_options.h"
#include "smt/command.h"
#include "smt/dump.h"
#include "smt/set_defaults.h"
#include "util/resource_manager.h"

namespace CVC4 {
namespace smt {

OptionsManager::OptionsManager(Options* opts, ResourceManager* rm)
    : d_options(opts), d_resourceManager(rm)
{
  // set options that must take effect immediately
  if (opts->wasSetByUser(options::defaultExprDepth))
  {
    notifySetOption(options::defaultExprDepth.getName());
  }
  if (opts->wasSetByUser(options::defaultDagThresh))
  {
    notifySetOption(options::defaultDagThresh.getName());
  }
  if (opts->wasSetByUser(options::printExprTypes))
  {
    notifySetOption(options::printExprTypes.getName());
  }
  if (opts->wasSetByUser(options::dumpModeString))
  {
    notifySetOption(options::dumpModeString.getName());
  }
  if (opts->wasSetByUser(options::printSuccess))
  {
    notifySetOption(options::printSuccess.getName());
  }
  if (opts->wasSetByUser(options::diagnosticChannelName))
  {
    notifySetOption(options::diagnosticChannelName.getName());
  }
  if (opts->wasSetByUser(options::regularChannelName))
  {
    notifySetOption(options::regularChannelName.getName());
  }
  if (opts->wasSetByUser(options::dumpToFileName))
  {
    notifySetOption(options::dumpToFileName.getName());
  }
  // set this as a listener to be notified of options changes from now on
  opts->setListener(this);
}

OptionsManager::~OptionsManager() {}

void OptionsManager::notifySetOption(const std::string& key)
{
  Trace("smt") << "SmtEnginePrivate::notifySetOption(" << key << ")"
               << std::endl;
  if (key == options::defaultExprDepth.getName())
  {
    int depth = (*d_options)[options::defaultExprDepth];
    Debug.getStream() << expr::ExprSetDepth(depth);
    Trace.getStream() << expr::ExprSetDepth(depth);
    Notice.getStream() << expr::ExprSetDepth(depth);
    Chat.getStream() << expr::ExprSetDepth(depth);
    Message.getStream() << expr::ExprSetDepth(depth);
    Warning.getStream() << expr::ExprSetDepth(depth);
    // intentionally exclude Dump stream from this list
  }
  else if (key == options::defaultDagThresh.getName())
  {
    int dag = (*d_options)[options::defaultDagThresh];
    Debug.getStream() << expr::ExprDag(dag);
    Trace.getStream() << expr::ExprDag(dag);
    Notice.getStream() << expr::ExprDag(dag);
    Chat.getStream() << expr::ExprDag(dag);
    Message.getStream() << expr::ExprDag(dag);
    Warning.getStream() << expr::ExprDag(dag);
    Dump.getStream() << expr::ExprDag(dag);
  }
  else if (key == options::printExprTypes.getName())
  {
    bool value = (*d_options)[options::printExprTypes];
    Debug.getStream() << expr::ExprPrintTypes(value);
    Trace.getStream() << expr::ExprPrintTypes(value);
    Notice.getStream() << expr::ExprPrintTypes(value);
    Chat.getStream() << expr::ExprPrintTypes(value);
    Message.getStream() << expr::ExprPrintTypes(value);
    Warning.getStream() << expr::ExprPrintTypes(value);
    // intentionally exclude Dump stream from this list
  }
  else if (key == options::dumpModeString.getName())
  {
    const std::string& value = (*d_options)[options::dumpModeString];
    Dump.setDumpFromString(value);
  }
  else if (key == options::printSuccess.getName())
  {
    bool value = (*d_options)[options::printSuccess];
    Debug.getStream() << Command::printsuccess(value);
    Trace.getStream() << Command::printsuccess(value);
    Notice.getStream() << Command::printsuccess(value);
    Chat.getStream() << Command::printsuccess(value);
    Message.getStream() << Command::printsuccess(value);
    Warning.getStream() << Command::printsuccess(value);
    *options::out() << Command::printsuccess(value);
  }
  else if (key == options::regularChannelName.getName())
  {
    d_managedRegularChannel.set(options::regularChannelName());
  }
  else if (key == options::diagnosticChannelName.getName())
  {
    d_managedDiagnosticChannel.set(options::diagnosticChannelName());
  }
  else if (key == options::dumpToFileName.getName())
  {
    d_managedDumpChannel.set(options::dumpToFileName());
  }
  // otherwise, no action is necessary
}

void OptionsManager::finishInit(LogicInfo& logic, bool isInternalSubsolver)
{
  // set up the timeouts and resource limits
  if ((*d_options)[options::perCallResourceLimit] != 0)
  {
    d_resourceManager->setResourceLimit(options::perCallResourceLimit(), false);
  }
  if ((*d_options)[options::cumulativeResourceLimit] != 0)
  {
    d_resourceManager->setResourceLimit(options::cumulativeResourceLimit(),
                                        true);
  }
  if ((*d_options)[options::perCallMillisecondLimit] != 0)
  {
    d_resourceManager->setTimeLimit(options::perCallMillisecondLimit());
  }
  // ensure that our heuristics are properly set up
  setDefaults(logic, isInternalSubsolver);
}

}  // namespace smt
}  // namespace CVC4
