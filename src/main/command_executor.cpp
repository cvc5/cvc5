/*********************                                                        */
/*! \file command_executor.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Kshitij Bansal
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#include <iostream>

#include "main/command_executor.h"
#include "expr/command.h"

#include "main/main.h"

#include "smt/options.h"

namespace CVC4 {
namespace main {

CommandExecutor::CommandExecutor(ExprManager &exprMgr, Options &options) :
  d_exprMgr(exprMgr),
  d_smtEngine(SmtEngine(&exprMgr)),
  d_options(options),
  d_stats("driver"),
  d_result() {
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

bool CommandExecutor::doCommandSingleton(Command* cmd)
{
  bool status = true;
  if(d_options[options::verbosity] >= -1) {
    status = smtEngineInvoke(&d_smtEngine, cmd, d_options[options::out]);
  } else {
    status = smtEngineInvoke(&d_smtEngine, cmd, NULL);
  }
  Result res;
  CheckSatCommand* cs = dynamic_cast<CheckSatCommand*>(cmd);
  if(cs != NULL) {
    d_result = res = cs->getResult();
  }
  QueryCommand* q = dynamic_cast<QueryCommand*>(cmd);
  if(q != NULL) {
    d_result = res = q->getResult();
  }
  // dump the model if option is set
  if( status &&
      d_options[options::produceModels] &&
      d_options[options::dumpModels] &&
      ( res.asSatisfiabilityResult() == Result::SAT ||
        (res.isUnknown() && res.whyUnknown() == Result::INCOMPLETE) ) ) {
    Command* gm = new GetModelCommand();
    status = doCommandSingleton(gm);
  }
  return status;
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
