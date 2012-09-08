/*********************                                                        */
/*! \file command_executor_portfolio.h
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
 **
 ** The portfolio executer branches check-sat queries to several
 ** threads.
 **/

#ifndef __CVC4__MAIN__COMMAND_EXECUTOR_PORTFOLIO_H
#define __CVC4__MAIN__COMMAND_EXECUTOR_PORTFOLIO_H

#include "main/command_executor.h"
#include "main/portfolio_util.h"

namespace CVC4 {

class CommandSequence;

namespace main {

class CommandExecutorPortfolio : public CommandExecutor {

  // These shall be created/deleted during initalization
  std::vector<ExprManager*> d_exprMgrs;
  const unsigned d_numThreads;   // Currently const, but designed so it is
                                 // not too hard to support this changing
  std::vector<SmtEngine*> d_smts;
  CommandSequence* d_seq;
  std::vector<Options>& d_threadOptions;
  std::vector<ExprManagerMapCollection*> d_vmaps;

  int d_lastWinner;

  // These shall be reset for each check-sat
  std::vector< SharedChannel<ChannelFormat>* > d_channelsOut;
  std::vector< SharedChannel<ChannelFormat>* > d_channelsIn;
  std::vector<std::ostringstream*> d_ostringstreams;

public:
  CommandExecutorPortfolio(ExprManager &exprMgr,
                           Options &options,
                           std::vector<Options>& tOpts);

  ~CommandExecutorPortfolio();

  std::string getSmtEngineStatus();
protected:
  bool doCommandSingleton(Command* cmd);
private:
  CommandExecutorPortfolio();
  void lemmaSharingInit();
  void lemmaSharingCleanup();
};/* class CommandExecutorPortfolio */

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif  /* __CVC4__MAIN__COMMAND_EXECUTOR_PORTFOLIO_H */
