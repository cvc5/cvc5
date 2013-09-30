/*********************                                                        */
/*! \file command_executor.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Kshitij Bansal
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#ifndef __CVC4__MAIN__COMMAND_EXECUTOR_H
#define __CVC4__MAIN__COMMAND_EXECUTOR_H

#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "util/statistics_registry.h"
#include "options/options.h"
#include "expr/command.h"

#include <string>
#include <iostream>

namespace CVC4 {
namespace main {

class CommandExecutor {

protected:
  ExprManager& d_exprMgr;
  SmtEngine d_smtEngine;
  Options& d_options;
  StatisticsRegistry d_stats;
  Result d_result;

public:
  CommandExecutor(ExprManager &exprMgr, Options &options);

  virtual ~CommandExecutor() {}

  /**
   * Executes a command. Recursively handles if cmd is a command
   * sequence.  Eventually uses doCommandSingleton (which can be
   * overridden by a derived class).
   */
  bool doCommand(CVC4::Command* cmd);

  Result getResult() const { return d_result; }

  StatisticsRegistry& getStatisticsRegistry() {
    return d_stats;
  }

  virtual void flushStatistics(std::ostream& out) const {
    d_exprMgr.getStatistics().flushInformation(out);
    d_smtEngine.getStatistics().flushInformation(out);
    d_stats.flushInformation(out);
  }

protected:
  /** Executes treating cmd as a singleton */
  virtual bool doCommandSingleton(CVC4::Command* cmd);

private:
  CommandExecutor();

};/* class CommandExecutor */

bool smtEngineInvoke(SmtEngine* smt,
                     Command* cmd,
                     std::ostream *out);

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif  /* __CVC4__MAIN__COMMAND_EXECUTOR_H */
