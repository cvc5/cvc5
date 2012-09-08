/*********************                                                        */
/*! \file command_executor.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#ifndef __CVC4__MAIN__COMMAND_EXECUTOR_H
#define __CVC4__MAIN__COMMAND_EXECUTOR_H

#include "expr/expr_manager.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace main {

class CommandExecutor {

protected:
  ExprManager& d_exprMgr;
  SmtEngine d_smtEngine;
  Options& d_options;

public:
  // Note: though the options are not cached (instead a reference is
  // used), the portfolio command executer currently parses them
  // during initalization, creating thread-specific options and
  // storing them
  CommandExecutor(ExprManager &exprMgr, Options &options);

  ~CommandExecutor() {}

  /**
   * Executes a command. Recursively handles if cmd is a command
   * sequence.  Eventually uses doCommandSingleton (which can be
   * overridden by a derived class).
   */
  bool doCommand(CVC4::Command* cmd);

  virtual std::string getSmtEngineStatus();

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
