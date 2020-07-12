/*********************                                                        */
/*! \file options_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Module for managing options of an SmtEngine.
 **/

#include "smt/options_manager.h"

#include "smt/command.h"
#include "expr/expr_iomanip.h"
#include "base/output.h"
#include "smt/dump.h"
#include "options/smt_options.h"
#include "options/expr_options.h"
#include "options/base_options.h"

namespace CVC4 {
namespace smt {

OptionsManager::OptionsManager(Options& opts) : d_options(opts){}

OptionsManager::~OptionsManager(){}

void OptionsManager::initialize()
{
  // set options that must take effect immediately
  if (d_options.wasSetByUser(options::defaultExprDepth))
  {
    setOption(options::defaultExprDepth.getName(), "");
  }
  if (d_options.wasSetByUser(options::defaultDagThresh))
  {
    setOption(options::defaultDagThresh.getName(), "");
  }
  if (d_options.wasSetByUser(options::printExprTypes))
  {
    setOption(options::printExprTypes.getName(), "");
  }
  if (d_options.wasSetByUser(options::dumpModeString))
  {
    setOption(options::dumpModeString.getName(), "");
  }
  if (d_options.wasSetByUser(options::printSuccess))
  {
    setOption(options::printSuccess.getName(), "");
  }
}

void OptionsManager::setOption(const std::string& key, const std::string& optarg)
{
  Trace("smt") << "SmtEnginePrivate::setOption(" << key << ", " << optarg
                << ")" << std::endl;
  if (key == options::defaultExprDepth.getName())
  {
    int depth = d_options[options::defaultExprDepth];
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
    int dag = options::defaultDagThresh();
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
    bool value = d_options[options::printExprTypes];
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
    const std::string& value = d_options[options::dumpModeString];
    Dump.setDumpFromString(value);
  }
  else if (key == options::printSuccess.getName())
  {
    bool value = d_options[options::printSuccess];
    Debug.getStream() << Command::printsuccess(value);
    Trace.getStream() << Command::printsuccess(value);
    Notice.getStream() << Command::printsuccess(value);
    Chat.getStream() << Command::printsuccess(value);
    Message.getStream() << Command::printsuccess(value);
    Warning.getStream() << Command::printsuccess(value);
    *options::out() << Command::printsuccess(value);
  }
  // otherwise, no action is necessary
}

}  // namespace smt
}  // namespace CVC4

