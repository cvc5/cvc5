/*********************                                                        */
/*! \file command_executor_portfolio.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **
 ** The portfolio executor branches check-sat queries to several
 ** threads.
 **/

#include "main/command_executor_portfolio.h"

#if HAVE_UNISTD_H
#  include <unistd.h>
#endif /* HAVE_UNISTD_H */

#include <boost/exception_ptr.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/thread.hpp>
#include <boost/thread/condition.hpp>
#include <string>

#include "cvc4autoconfig.h"
#include "expr/pickler.h"
#include "main/main.h"
#include "main/portfolio.h"
#include "options/options.h"
#include "options/set_language.h"
#include "smt/command.h"


using namespace std;

namespace CVC4 {
namespace main {

CommandExecutorPortfolio::CommandExecutorPortfolio(
    ExprManager &exprMgr, Options &options, OptionsList& tOpts)
    : CommandExecutor(exprMgr, options),
      d_numThreads(options.getThreads()),
      d_smts(),
      d_seq(new CommandSequence()),
      d_threadOptions(tOpts),
      d_vmaps(),
      d_lastWinner(0),
      d_channelsOut(),
      d_channelsIn(),
      d_ostringstreams(),
      d_statLastWinner("portfolio::lastWinner"),
      d_statWaitTime("portfolio::waitTime")
{
  assert(d_threadOptions.size() == d_numThreads);

  d_statLastWinner.setData(d_lastWinner);
  d_stats.registerStat(&d_statLastWinner);

  d_stats.registerStat(&d_statWaitTime);

  /* Duplication, individualization */
  d_exprMgrs.push_back(&d_exprMgr);
  for(unsigned i = 1; i < d_numThreads; ++i) {
    d_exprMgrs.push_back(new ExprManager(d_threadOptions[i]));
  }

  // Create the SmtEngine(s)
  d_smts.push_back(d_smtEngine);
  for(unsigned i = 1; i < d_numThreads; ++i) {
    d_smts.push_back(new SmtEngine(d_exprMgrs[i]));
  }

  assert(d_vmaps.size() == 0);
  for(unsigned i = 0; i < d_numThreads; ++i) {
    d_vmaps.push_back(new ExprManagerMapCollection());
  }
}

CommandExecutorPortfolio::~CommandExecutorPortfolio()
{
  assert(d_seq != NULL);
  delete d_seq;

  assert(d_smts.size() == d_numThreads);
  for(unsigned i = 1; i < d_numThreads; ++i) {
    // the 0-th one is responsibility of parent class

    delete d_smts[i];
    delete d_exprMgrs[i];
  }
  d_exprMgrs.clear();
  d_smts.clear();

  d_stats.unregisterStat(&d_statLastWinner);
  d_stats.unregisterStat(&d_statWaitTime);
}

void CommandExecutorPortfolio::lemmaSharingInit()
{
  /* Sharing channels */
  assert(d_channelsIn.size() == 0);
  assert(d_channelsOut.size() == 0);

  if(d_numThreads == 1) {
    // Disable sharing
    d_threadOptions[0].setSharingFilterByLength(0);
  } else {
    // Setup sharing channels
    const unsigned int sharingChannelSize = 1000000;

    for(unsigned i = 0; i < d_numThreads; ++i){
      d_channelsOut.push_back(
          new SynchronizedSharedChannel<ChannelFormat>(sharingChannelSize));
      d_channelsIn.push_back(
          new SynchronizedSharedChannel<ChannelFormat>(sharingChannelSize));
    }

    /* Lemma I/O channels */
    for(unsigned i = 0; i < d_numThreads; ++i) {
      int thread_id = d_threadOptions[i].getThreadId();
      string tag = "thread #" + boost::lexical_cast<string>(thread_id);
      LemmaOutputChannel* outputChannel =
          new PortfolioLemmaOutputChannel(tag, d_channelsOut[i], d_exprMgrs[i],
                                          d_vmaps[i]->d_from, d_vmaps[i]->d_to);
      LemmaInputChannel* inputChannel =
          new PortfolioLemmaInputChannel(tag, d_channelsIn[i], d_exprMgrs[i],
                                         d_vmaps[i]->d_from, d_vmaps[i]->d_to);
      d_smts[i]->channels()->setLemmaInputChannel(inputChannel);
      d_smts[i]->channels()->setLemmaOutputChannel(outputChannel);
    }

    /* Output to string stream  */
    assert(d_ostringstreams.size() == 0);
    for(unsigned i = 0; i < d_numThreads; ++i) {
      d_ostringstreams.push_back(new ostringstream);
      d_threadOptions[i].setOut(d_ostringstreams[i]);

      OutputLanguage outputLanguage = d_threadOptions[i].getOutputLanguage();
      // important even for muzzled builds (to get result output right)
      *(d_threadOptions[i].getOut()) << language::SetLanguage(outputLanguage);
    }
  }
}/* CommandExecutorPortfolio::lemmaSharingInit() */

void CommandExecutorPortfolio::lemmaSharingCleanup()
{
  assert(d_numThreads == d_options.getThreads());

  if(d_numThreads == 1)
    return;

  // Channel cleanup
  assert(d_channelsIn.size() == d_numThreads);
  assert(d_channelsOut.size() == d_numThreads);
  for(unsigned i = 0; i < d_numThreads; ++i) {
    delete d_channelsIn[i];
    delete d_channelsOut[i];
    delete d_smts[i]->channels()->getLemmaInputChannel();
    d_smts[i]->channels()->setLemmaInputChannel(NULL);
    delete d_smts[i]->channels()->getLemmaOutputChannel();
    d_smts[i]->channels()->setLemmaOutputChannel(NULL);
  }
  d_channelsIn.clear();
  d_channelsOut.clear();

  // sstreams cleanup (if used)
  if(d_ostringstreams.size() != 0) {
    assert(d_ostringstreams.size() == d_numThreads);
    for(unsigned i = 0; i < d_numThreads; ++i) {
      d_threadOptions[i].setOut(d_options.getOut());
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
  // mode = 0 : run command on lastWinner, saving the command
  // to be run on all others
  //
  // mode = 1 : run a race of the command, update lastWinner
  //
  // mode = 2 : run _only_ the lastWinner thread, not saving the
  // command

  if(dynamic_cast<CheckSatCommand*>(cmd) != NULL ||
     dynamic_cast<QueryCommand*>(cmd) != NULL ||
     dynamic_cast<CheckSynthCommand*>(cmd) != NULL) {
    mode = 1;
  } else if(dynamic_cast<GetValueCommand*>(cmd) != NULL ||
            dynamic_cast<GetAssignmentCommand*>(cmd) != NULL ||
            dynamic_cast<GetModelCommand*>(cmd) != NULL ||
            dynamic_cast<GetProofCommand*>(cmd) != NULL ||
            dynamic_cast<GetInstantiationsCommand*>(cmd) != NULL ||
            dynamic_cast<GetUnsatCoreCommand*>(cmd) != NULL ||
            dynamic_cast<GetAssertionsCommand*>(cmd) != NULL ||
            dynamic_cast<GetInfoCommand*>(cmd) != NULL ||
            dynamic_cast<GetOptionCommand*>(cmd) != NULL ||
            false) {
    mode = 2;
  }

  Debug("portfolio::outputmode") << "Mode is " << mode
                                 << "lastWinner is " << d_lastWinner
                                 << "d_seq is " << d_seq << std::endl;

  if(mode == 0) {
    d_seq->addCommand(cmd->clone());
    Command* cmdExported =
      d_lastWinner == 0 ?
      cmd : cmd->exportTo(d_exprMgrs[d_lastWinner], *(d_vmaps[d_lastWinner]) );
    std::ostream* winnersOut =  d_options.getVerbosity() >= -1 ?
        (d_threadOptions[d_lastWinner]).getOut() : NULL;
    bool ret = smtEngineInvoke(d_smts[d_lastWinner], cmdExported, winnersOut);
    if(d_lastWinner != 0) delete cmdExported;
    return ret;
  } else if(mode == 1) {               // portfolio
    d_seq->addCommand(cmd->clone());

    // We currently don't support changing number of threads for each
    // command, but things have been architected in a way so that this
    // can be achieved without a lot of work.
    Command *seqs[d_numThreads];

    if(d_lastWinner == 0)
      seqs[0] = cmd;
    else
      seqs[0] = d_seq;

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
        seqs[i] =
          int(i) == d_lastWinner ?
          cmd->exportTo(d_exprMgrs[i], *(d_vmaps[i])) :
          d_seq->exportTo(d_exprMgrs[i], *(d_vmaps[i]) );
      } catch(ExportUnsupportedException& e) {
        if(d_options.getFallbackSequential()) {
          Notice() << "Unsupported theory encountered."
                   << "Switching to sequential mode.";
          return CommandExecutor::doCommandSingleton(cmd);
        }
        else
          throw Exception("Certain theories (e.g., datatypes) are (currently)"
                          " unsupported in portfolio\n mode. Please see option"
                          " --fallback-sequential to make this a soft error.");
      }
    }

    /**
     * Create identity variable map for the first thread, with only
     * those variables which have a corresponding variable in
     * another thread. (TODO: Also assert, all threads have the same
     * set of variables mapped.)
     */
    if(d_numThreads >= 2) {
      VarMap& thread_0_from = d_vmaps[0]->d_from;
      VarMap& thread_1_to = d_vmaps[1]->d_to;
      for(VarMap::iterator i=thread_1_to.begin();
          i != thread_1_to.end(); ++i) {
        thread_0_from[i->first] = i->first;
      }
      d_vmaps[0]->d_to = thread_0_from;
    }

    lemmaSharingInit();

    /* Portfolio */
    boost::function<bool()>* fns = new boost::function<bool()>[d_numThreads];
    for(unsigned i = 0; i < d_numThreads; ++i) {
      std::ostream* current_out_or_null = d_options.getVerbosity() >= -1 ?
          d_threadOptions[i].getOut() : NULL;

      fns[i] = boost::bind(smtEngineInvoke, d_smts[i], seqs[i],
                           current_out_or_null);
    }

    assert(d_channelsIn.size() == d_numThreads
           || d_numThreads == 1);
    assert(d_channelsOut.size() == d_numThreads
           || d_numThreads == 1);
    assert(d_smts.size() == d_numThreads);
    assert( !d_statWaitTime.running() );

    boost::function<void()>
      smFn = d_numThreads <= 1 ? boost::function<void()>() :
             boost::bind(sharingManager<ChannelFormat>,
                         d_numThreads,
                         &d_channelsOut[0],
                         &d_channelsIn[0],
                         &d_smts[0]);

    size_t threadStackSize = d_options.getThreadStackSize();
    threadStackSize *= 1024 * 1024;

    pair<int, bool> portfolioReturn =
        runPortfolio(d_numThreads, smFn, fns, threadStackSize,
                     d_options.getWaitToJoin(), d_statWaitTime);

#ifdef CVC4_STATISTICS_ON
    assert( d_statWaitTime.running() );
    d_statWaitTime.stop();
#endif /* CVC4_STATISTICS_ON */

    d_lastWinner = portfolioReturn.first;
    d_result = d_smts[d_lastWinner]->getStatusOfLastCommand();

    if(d_ostringstreams.size() != 0) {
      assert(d_numThreads == d_options.getThreads());
      assert(portfolioReturn.first >= 0);
      assert(unsigned(portfolioReturn.first) < d_numThreads);

      std::ostream& out = *d_options.getOut();
      if(Debug.isOn("treat-unknown-error")) {
        if(d_ostringstreams[portfolioReturn.first]->str() == "unknown\n") {
          out << "portfolioReturn = (" << portfolioReturn.first << ", "
              << portfolioReturn.second << ")\n";
          for(unsigned i = 0; i < d_numThreads; ++i)
            out << "thread " << i << ": " << d_ostringstreams[i]->str()
                << std::endl;
          throw Exception("unknown encountered");
        }
      }

      out << d_ostringstreams[portfolioReturn.first]->str()
          << std::flush;

#ifdef CVC4_COMPETITION_MODE
      // We use CVC4 in competition with --no-wait-to-join. If
      // destructors run, they will destroy(!) us. So, just exit now.
      _exit(0);
#endif /* CVC4_COMPETITION_MODE */
    }

    /* cleanup this check sat specific stuff */
    lemmaSharingCleanup();

    delete d_seq;
    d_seq = new CommandSequence();

    delete[] fns;

    bool status = portfolioReturn.second;

    // dump the model/proof/unsat core if option is set
    if(status) {
      if( d_options.getProduceModels() &&
          d_options.getDumpModels() &&
          ( d_result.asSatisfiabilityResult() == Result::SAT ||
            (d_result.isUnknown() &&
             d_result.whyUnknown() == Result::INCOMPLETE) ) )
      {
        Command* gm = new GetModelCommand();
        status = doCommandSingleton(gm);
      } else if( d_options.getProof() &&
                 d_options.getDumpProofs() &&
                 d_result.asSatisfiabilityResult() == Result::UNSAT ) {
        Command* gp = new GetProofCommand();
        status = doCommandSingleton(gp);
      } else if( d_options.getDumpInstantiations() &&
                 ( ( d_options.getInstFormatMode() != INST_FORMAT_MODE_SZS &&
                   ( d_result.asSatisfiabilityResult() == Result::SAT ||
                     (d_result.isUnknown() &&
                      d_result.whyUnknown() == Result::INCOMPLETE) ) ) ||
                   d_result.asSatisfiabilityResult() == Result::UNSAT ) ) {
        Command* gi = new GetInstantiationsCommand();
        status = doCommandSingleton(gi);
      } else if( d_options.getDumpSynth() &&
                 d_result.asSatisfiabilityResult() == Result::UNSAT ){
        Command* gi = new GetSynthSolutionCommand();
        status = doCommandSingleton(gi);
      } else if( d_options.getDumpUnsatCores() &&
                 d_result.asSatisfiabilityResult() == Result::UNSAT ) {
        Command* guc = new GetUnsatCoreCommand();
        status = doCommandSingleton(guc);
      }
    }

    return status;
  } else if(mode == 2) {
    Command* cmdExported = d_lastWinner == 0 ?
        cmd : cmd->exportTo(d_exprMgrs[d_lastWinner], *(d_vmaps[d_lastWinner]));
    std::ostream* winner_out_if_verbose = d_options.getVerbosity() >= -1 ?
        d_threadOptions[d_lastWinner].getOut() : NULL;
    bool ret = smtEngineInvoke(d_smts[d_lastWinner], cmdExported,
                               winner_out_if_verbose);
    if(d_lastWinner != 0){
      delete cmdExported;
    }
    return ret;
  } else {
    // Unreachable();
    assert(false);
    return false;
  }

}/* CommandExecutorPortfolio::doCommandSingleton() */

void CommandExecutorPortfolio::flushStatistics(std::ostream& out) const {
  assert(d_numThreads == d_exprMgrs.size() &&
         d_exprMgrs.size() == d_smts.size());
  for(size_t i = 0; i < d_numThreads; ++i) {
    string emTag = "thread#"
        + boost::lexical_cast<string>(d_threadOptions[i].getThreadId());
    Statistics stats = d_exprMgrs[i]->getStatistics();
    stats.setPrefix(emTag);
    stats.flushInformation(out);

    string smtTag = "thread#"
        + boost::lexical_cast<string>(d_threadOptions[i].getThreadId());
    stats = d_smts[i]->getStatistics();
    stats.setPrefix(smtTag);
    stats.flushInformation(out);
  }
  d_stats.flushInformation(out);
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
