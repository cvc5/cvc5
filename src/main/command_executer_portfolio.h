/*********************                                                        */
/*! \file command_executer_portfolio.h
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
 **
 ** The portfolio executer branches check-sat queries to several
 ** threads.
 **/

#ifndef __CVC4__COMMAND_EXECUTER_PORTFOLIO_H
#define __CVC4__COMMAND_EXECUTER_PORTFOLIO_H

#include "main/command_executer.h"
#include "main/portfolio_util.h"

namespace CVC4 {

class CommandSequence;

namespace main {

class CommandExecuterPortfolio : public CommandExecuter {

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
  CommandExecuterPortfolio(ExprManager &exprMgr,
                           Options &options,
                           std::vector<Options>& tOpts);

  ~CommandExecuterPortfolio();

  std::string getSmtEngineStatus();
protected:
  bool doCommandSingleton(Command* cmd);
private:
  CommandExecuterPortfolio();
  void lemmaSharingInit();
  void lemmaSharingCleanup();
};

}/*main namespace*/
}/*CVC4 namespace*/

#endif  /* __CVC4__COMMAND_EXECUTER_PORTFOLIO_H */
