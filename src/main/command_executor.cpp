/*********************                                                        */
/*! \file command_executor.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#include <iostream>

#include "main/command_executor.h"
#include "expr/command.h"

#include "main/main.h"

namespace CVC4 {
namespace main {

CommandExecutor::CommandExecutor(ExprManager &exprMgr, Options &options):
  d_exprMgr(exprMgr),
  d_smtEngine(SmtEngine(&exprMgr)),
  d_options(options),
  d_stats("driver") {
}

bool CommandExecutor::doCommand(Command* cmd)
{
  if( d_options[options::parseOnly] ) {
    return true;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    // assume no error
    bool status = true;

    for(CommandSequence::iterator subcmd = seq->begin();
        status && subcmd != seq->end();
        ++subcmd) {
      status = doCommand(*subcmd);
    }

    return status;
  } else {
    if(d_options[options::verbosity] > 2) {
      *d_options[options::out] << "Invoking: " << *cmd << std::endl;
    }

    return doCommandSingleton(cmd);
  }
}

bool CommandExecutor::doCommandSingleton(Command *cmd)
{
  bool status = true;
  if(d_options[options::verbosity] >= 0) {
    status = smtEngineInvoke(&d_smtEngine, cmd, d_options[options::out]);
  } else {
    status = smtEngineInvoke(&d_smtEngine, cmd, NULL);
  }
  return status;
}

std::string CommandExecutor::getSmtEngineStatus()
{
  return d_smtEngine.getInfo("status").getValue();
}

bool smtEngineInvoke(SmtEngine* smt, Command* cmd, std::ostream *out)
{
  if(out == NULL) {
    cmd->invoke(smt);
  } else {
    cmd->invoke(smt, *out);
  }
  return !cmd->fail();
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
