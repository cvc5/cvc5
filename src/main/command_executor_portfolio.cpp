/*********************                                                        */
/*! \file command_executor_portfolio.cpp
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

#include <boost/thread.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>
#include <boost/lexical_cast.hpp>
#include <string>

#include "expr/command.h"
#include "expr/pickler.h"
#include "main/command_executor_portfolio.h"
#include "main/main.h"
#include "main/options.h"
#include "main/portfolio.h"
#include "options/options.h"
#include "smt/options.h"

using namespace std;

namespace CVC4 {
namespace main {

CommandExecutorPortfolio::CommandExecutorPortfolio
(ExprManager &exprMgr, Options &options, vector<Options>& tOpts):
  CommandExecutor(exprMgr, options),
  d_numThreads(options[options::threads]),
  d_smts(),
  d_seq(new CommandSequence()),
  d_threadOptions(tOpts),
  d_vmaps(),
  d_lastWinner(0),
  d_channelsOut(),
  d_channelsIn(),
  d_ostringstreams()
{
  Assert(d_threadOptions.size() == d_numThreads);

  /* Duplication, Individualisation */
  d_exprMgrs.push_back(&d_exprMgr);
  for(unsigned i = 1; i < d_numThreads; ++i) {
    d_exprMgrs.push_back(new ExprManager(d_threadOptions[i]));
  }

  // Create the SmtEngine(s)
  d_smts.push_back(&d_smtEngine);
  for(unsigned i = 1; i < d_numThreads; ++i) {
    d_smts.push_back(new SmtEngine(d_exprMgrs[i]));
  }

  Assert(d_vmaps.size() == 0);
  for(unsigned i = 0; i < d_numThreads; ++i) {
    d_vmaps.push_back(new ExprManagerMapCollection());
  }
}

CommandExecutorPortfolio::~CommandExecutorPortfolio()
{
  Assert(d_seq != NULL);
  delete d_seq;

  Assert(d_smts.size() == d_numThreads);
  for(unsigned i = 1; i < d_numThreads; ++i) {
    // the 0-th one is responsibility of parent class

    delete d_exprMgrs[i];
    delete d_smts[i];
  }
  d_exprMgrs.clear();
  d_smts.clear();
}

void CommandExecutorPortfolio::lemmaSharingInit()
{
  /* Sharing channels */
  Assert(d_channelsIn.size() == 0);
  Assert(d_channelsOut.size() == 0);

  if(d_numThreads == 1) {
    // Disable sharing
    d_threadOptions[0].set(options::sharingFilterByLength, 0);
  } else {
    // Setup sharing channels
    const unsigned int sharingChannelSize = 1000000;

    for(unsigned i = 0; i < d_numThreads; ++i){
      if(Debug.isOn("channel-empty")) {
        d_channelsOut.push_back
          (new EmptySharedChannel<ChannelFormat>(sharingChannelSize));
        d_channelsIn.push_back
          (new EmptySharedChannel<ChannelFormat>(sharingChannelSize));
        continue;
      }
      d_channelsOut.push_back
        (new SynchronizedSharedChannel<ChannelFormat>(sharingChannelSize));
      d_channelsIn.push_back
        (new SynchronizedSharedChannel<ChannelFormat>(sharingChannelSize));
    }

    /* Lemma I/O channels */
    for(unsigned i = 0; i < d_numThreads; ++i) {
      string tag = "thread #" +
        boost::lexical_cast<string>(d_threadOptions[i][options::thread_id]);
      d_threadOptions[i].set
        (options::lemmaOutputChannel,
         new PortfolioLemmaOutputChannel(tag, d_channelsOut[i], d_exprMgrs[i],
                                         d_vmaps[i]->d_from, d_vmaps[i]->d_to));
      d_threadOptions[i].set
        (options::lemmaInputChannel,
         new PortfolioLemmaInputChannel(tag, d_channelsIn[i], d_exprMgrs[i],
                                        d_vmaps[i]->d_from, d_vmaps[i]->d_to));
    }

    /* Output to string stream  */
    if(d_options[options::verbosity] == 0
       || d_options[options::separateOutput]) {
      Assert(d_ostringstreams.size() == 0);
      for(unsigned i = 0; i < d_numThreads; ++i) {
        d_ostringstreams.push_back(new ostringstream);
        d_threadOptions[i].set(options::out, d_ostringstreams[i]);
      }
    }
  }
}/* CommandExecutorPortfolio::lemmaSharingInit() */

void CommandExecutorPortfolio::lemmaSharingCleanup()
{
  Assert(d_numThreads == d_options[options::threads]);

  // Channel cleanup
  Assert(d_channelsIn.size() == d_numThreads);
  Assert(d_channelsOut.size() == d_numThreads);
  for(unsigned i = 0; i < d_numThreads; ++i) {
    delete d_channelsIn[i];
    delete d_channelsOut[i];
    d_threadOptions[i].set(options::lemmaInputChannel, NULL);
    d_threadOptions[i].set(options::lemmaOutputChannel, NULL);
  }
  d_channelsIn.clear();
  d_channelsOut.clear();

  // sstreams cleanup (if used)
  if(d_ostringstreams.size() != 0) {
    Assert(d_ostringstreams.size() == d_numThreads);
    for(unsigned i = 0; i < d_numThreads; ++i) {
      d_threadOptions[i].set(options::out, d_options[options::out]);
      delete d_ostringstreams[i];
    }
    d_ostringstreams.clear();
  }

}/* CommandExecutorPortfolio::lemmaSharingCleanup() */


bool CommandExecutorPortfolio::doCommandSingleton(Command* cmd)
{
  /**
   * save the command and if check sat or query command, run a
   * porfolio of SMT solvers.
   */

  int mode = 0;
  // mode = 0 : run the first thread
  // mode = 1 : run a porfolio
  // mode = 2 : run the last winner

  // if(dynamic_cast<CheckSatCommand*>(cmd) != NULL ||
  //    dynamic_cast<QueryCommand*>(cmd) != NULL) {
  //   mode = 1;
  // } else if(dynamic_cast<GetValueCommand*>(cmd) != NULL) {
  //   mode = 2;
  // }

  if(mode == 0) {
    d_seq->addCommand(cmd->clone());
    return CommandExecutor::doCommandSingleton(cmd);
  } else if(mode == 1) {               // portfolio
    d_seq->addCommand(cmd->clone());

    // We currently don't support changing number of threads for each
    // command, but things have been architected in a way so that this
    // can be acheived with not a lot of work
    Command *seqs[d_numThreads];

    seqs[0] = cmd;

    /* variable maps and exporting */
    for(unsigned i = 1; i < d_numThreads; ++i) {
      /**
       * vmaps[i].d_from [x] = y means
       *    that in thread #0's expr manager id is y
       *    and  in thread #i's expr manager id is x
       * opposite for d_to
       *
       * d_from[x] : in a sense gives the id if converting *from* it to
       *             first thread
       */
      try {
        seqs[i] = d_seq->exportTo(d_exprMgrs[i], *(d_vmaps[i]) );
      }catch(ExportToUnsupportedException& e){
        return CommandExecutor::doCommandSingleton(cmd);
      }
    }

    /**
     * Create identity variable map for the first thread, with only
     * those variables which have a corresponding variable in
     * another thread. (TODO: Also assert, all threads have the same
     * set of variables mapped.)
     */
    if(d_numThreads >= 2) {
      for(typeof(d_vmaps[1]->d_to.begin()) i=d_vmaps[1]->d_to.begin();
          i!=d_vmaps[1]->d_to.end(); ++i) {
        (d_vmaps[0]->d_from)[i->first] = i->first;
      }
      d_vmaps[0]->d_to = d_vmaps[0]->d_from;
    }

    lemmaSharingInit();

    /* Portfolio */
    boost::function<bool()> fns[d_numThreads];
    for(unsigned i = 0; i < d_numThreads; ++i) {
      fns[i] = boost::bind(smtEngineInvoke,
                           d_smts[i],
                           seqs[i],
                           d_threadOptions[i][options::out]
                           );
    }

    Assert(d_channelsIn.size() == d_numThreads);
    Assert(d_channelsOut.size() == d_numThreads);
    Assert(d_smts.size() == d_numThreads);
    boost::function<void()>
      smFn = boost::bind(sharingManager<ChannelFormat>,
                         d_numThreads,
                         &d_channelsOut[0],
                         &d_channelsIn[0],
                         &d_smts[0]);

    pair<int, bool> portfolioReturn =
        runPortfolio(d_numThreads, smFn, fns, true);

    d_seq = NULL;
    delete d_seq;
    d_seq = new CommandSequence();

    d_lastWinner = portfolioReturn.first;

    // *d_options[options::out]
    //   << "Winner = "
    //   << portfolioReturn.first
    //   << std::endl;

    if(d_ostringstreams.size() != 0) {
      Assert(d_numThreads == d_options[options::threads]);
      Assert(portfolioReturn.first >= 0);
      Assert(unsigned(portfolioReturn.first) < d_numThreads);

      *d_options[options::out]
        << d_ostringstreams[portfolioReturn.first]->str();
    }

    /* cleanup this check sat specific stuff */
    lemmaSharingCleanup();

    return portfolioReturn.second;
  } else if(mode == 2) {
    return smtEngineInvoke(d_smts[d_lastWinner],
                           cmd,
                           d_threadOptions[d_lastWinner][options::out]);
  } else {
    Unreachable();
  }

}/* CommandExecutorPortfolio::doCommandSingleton() */

std::string CommandExecutorPortfolio::getSmtEngineStatus()
{
  return d_smts[d_lastWinner]->getInfo("status").getValue();
}

void CommandExecutorPortfolio::flushStatistics(std::ostream& out) const {
  Assert(d_numThreads == d_exprMgrs.size() && d_exprMgrs.size() == d_smts.size());
  for(size_t i = 0; i < d_numThreads; ++i) {
    string emTag = "ExprManager thread #"
      + boost::lexical_cast<string>(d_threadOptions[i][options::thread_id]);
    Statistics stats = d_exprMgrs[i]->getStatistics();
    stats.setPrefix(emTag);
    stats.flushInformation(out);

    string smtTag = "SmtEngine thread #"
      + boost::lexical_cast<string>(d_threadOptions[i][options::thread_id]);
    stats = d_smts[i]->getStatistics();
    stats.setPrefix(smtTag);
    stats.flushInformation(out);
  }
  d_stats.flushInformation(out);
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
