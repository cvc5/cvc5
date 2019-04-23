/*********************                                                        */
/*! \file command_executor_portfolio.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

#include <iosfwd>
#include <sstream>
#include <string>
#include <vector>

namespace CVC4 {

class CommandSequence;

namespace api {
class Solver;
}

namespace main {

class CommandExecutorPortfolio : public CommandExecutor {
  // Solvers are created/deleted during initialization
  std::vector<api::Solver*> d_solvers;

  std::vector<ExprManager*> d_exprMgrs;
  const unsigned d_numThreads;   // Currently const, but designed so it is
                                 // not too hard to support this changing
  std::vector<SmtEngine*> d_smts;
  CommandSequence* d_seq;
  OptionsList& d_threadOptions;
  std::vector<ExprManagerMapCollection*> d_vmaps;

  int d_lastWinner;

  // These shall be reset for each check-sat
  std::vector< SharedChannel<ChannelFormat>* > d_channelsOut;
  std::vector< SharedChannel<ChannelFormat>* > d_channelsIn;
  std::vector<std::ostringstream*> d_ostringstreams;

  // Stats
  ReferenceStat<int> d_statLastWinner;
  TimerStat d_statWaitTime;

public:
 CommandExecutorPortfolio(api::Solver* solver,
                          Options& options,
                          OptionsList& tOpts);

 ~CommandExecutorPortfolio();

 std::string getSmtEngineStatus();

 void flushStatistics(std::ostream& out) const override;

protected:
 bool doCommandSingleton(Command* cmd) override;

private:
  CommandExecutorPortfolio();
  void lemmaSharingInit();
  void lemmaSharingCleanup();
};/* class CommandExecutorPortfolio */

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif  /* __CVC4__MAIN__COMMAND_EXECUTOR_PORTFOLIO_H */
