/*********************                                                        */
/*! \file command_executer.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: mdeters
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#ifndef __CVC4__COMMAND_EXECUTER_H
#define __CVC4__COMMAND_EXECUTER_H

#include "expr/expr_manager.h"
#include "smt/smt_engine.h"

namespace CVC4 {

namespace main {

class CommandExecuter {

protected:
  ExprManager& d_exprMgr;
  SmtEngine d_smtEngine;
  Options& d_options;

public:
  // Note: though the options are not cached (instead a reference is
  // used), the portfolio command executer currently parses them
  // during initalization, creating thread-specific options and
  // storing them
  CommandExecuter(ExprManager &exprMgr, Options &options);

  ~CommandExecuter() {}

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
  CommandExecuter();

};

bool smtEngineInvoke(SmtEngine* smt,
                     Command* cmd,
                     std::ostream *out);


}/*main namespace*/
}/*CVC4 namespace*/

#endif  /* __CVC4__COMMAND_EXECUTER_H */
