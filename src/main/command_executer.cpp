/*********************                                                        */
/*! \file command_executer.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
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

#include <iostream>

#include "main/command_executer.h"
#include "expr/command.h"

#include "main/main.h"

namespace CVC4 {
namespace main {


CommandExecuter::CommandExecuter(ExprManager &exprMgr, Options &options):
  d_exprMgr(exprMgr),
  d_smtEngine(SmtEngine(&exprMgr)),
  d_options(options) {
  
  // signal handlers need access
  main::pStatistics = d_smtEngine.getStatisticsRegistry();
  d_exprMgr.getStatisticsRegistry()->setName("ExprManager");
  main::pStatistics->registerStat_(d_exprMgr.getStatisticsRegistry());
}

bool CommandExecuter::doCommand(Command* cmd)
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
    if(d_options[options::verbosity] > 0) {
      *d_options[options::out] << "Invoking: " << *cmd << std::endl;
    }

    return doCommandSingleton(cmd);
  }
}

bool CommandExecuter::doCommandSingleton(Command *cmd)
{
  bool status = true;
  if(d_options[options::verbosity] >= 0) {
    status = smtEngineInvoke(&d_smtEngine, cmd, d_options[options::out]);
  } else {
    status = smtEngineInvoke(&d_smtEngine, cmd, NULL);
  }
  return status;
}

std::string CommandExecuter::getSmtEngineStatus()
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

}/*main namespace*/
}/*CVC4 namespace*/
