/*********************                                                        */
/*! \file driver_portfolio.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: taking, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Driver for portfolio CVC4 executable (pcvc4)
 **
 ** Driver for portfolio CVC4 executable (pcvc4).
 **/

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <sys/time.h>           // for gettimeofday()

#include <queue>

#include <boost/thread.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>
#include <boost/lexical_cast.hpp>

#include "cvc4autoconfig.h"
#include "main/main.h"
#include "main/interactive_shell.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "expr/variable_type_map.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/Assert.h"
#include "util/configuration.h"
#include "options/options.h"
#include "main/options.h"
#include "smt/options.h"
#include "prop/options.h"
#include "theory/uf/options.h"
#include "util/output.h"
#include "util/dump.h"
#include "util/result.h"
#include "util/stats.h"
#include "util/lemma_input_channel.h"
#include "util/lemma_output_channel.h"

#include "expr/pickler.h"
#include "util/channel.h"

#include "main/portfolio.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

/* Global variables */

namespace CVC4 {
  namespace main {

    StatisticsRegistry theStatisticsRegistry;

    /** A pointer to the StatisticsRegistry (the signal handlers need it) */
    CVC4::StatisticsRegistry* pStatistics;

  }/* CVC4::main namespace */
}/* CVC4 namespace */

/* Function declarations */

static bool doCommand(SmtEngine&, Command*, Options&);

Result doSmt(SmtEngine &smt, Command *cmd, Options &options);

template<typename T>
void sharingManager(unsigned numThreads,
                    SharedChannel<T>* channelsOut[],
                    SharedChannel<T>* channelsIn[],
                    SmtEngine* smts[]);


/* To monitor for activity on shared channels */
bool global_activity;
bool global_activity_true() { return global_activity; }
bool global_activity_false() { return not global_activity; }
boost::condition global_activity_cond;

typedef expr::pickle::Pickle channelFormat; /* Remove once we are using Pickle */

template <typename T>
class EmptySharedChannel: public SharedChannel<T> {
public:
  EmptySharedChannel(int) {}
  bool push(const T&) { return true; }
  T pop() { return T(); }
  bool empty() { return true; }
  bool full() { return false; }
};

class PortfolioLemmaOutputChannel : public LemmaOutputChannel {
private:
  string d_tag;
  SharedChannel<channelFormat>* d_sharedChannel;
  expr::pickle::MapPickler d_pickler;

public:
  int cnt;
  PortfolioLemmaOutputChannel(string tag,
                              SharedChannel<channelFormat> *c,
                              ExprManager* em,
                              VarMap& to,
                              VarMap& from) :
    d_tag(tag),
    d_sharedChannel(c),
    d_pickler(em, to, from)
    ,cnt(0)
  {}

  void notifyNewLemma(Expr lemma) {
    if(Debug.isOn("disable-lemma-sharing")) {
      return;
    }
    if(options::sharingFilterByLength() >= 0) { // 0 would mean no-sharing effectively
      if(int(lemma.getNumChildren()) > options::sharingFilterByLength()) {
        return;
      }
    }
    ++cnt;
    Trace("sharing") << d_tag << ": " << lemma << endl;
    expr::pickle::Pickle pkl;
    try {
      d_pickler.toPickle(lemma, pkl);
      d_sharedChannel->push(pkl);
      if(Trace.isOn("showSharing") && options::thread_id() == 0) {
        *options::out() << "thread #0: notifyNewLemma: " << lemma << endl;
      }
    } catch(expr::pickle::PicklingException& p){
      Trace("sharing::blocked") << lemma << endl;
    }
  }

};

/* class PortfolioLemmaInputChannel */
class PortfolioLemmaInputChannel : public LemmaInputChannel {
private:
  string d_tag;
  SharedChannel<channelFormat>* d_sharedChannel;
  expr::pickle::MapPickler d_pickler;

public:
  PortfolioLemmaInputChannel(string tag,
                             SharedChannel<channelFormat>* c,
                             ExprManager* em,
                             VarMap& to,
                             VarMap& from) :
    d_tag(tag),
    d_sharedChannel(c),
    d_pickler(em, to, from){
  }

  bool hasNewLemma(){
    Debug("lemmaInputChannel") << d_tag << ": " << "hasNewLemma" << endl;
    return !d_sharedChannel->empty();
  }

  Expr getNewLemma() {
    Debug("lemmaInputChannel") << d_tag << ": " << "getNewLemma" << endl;
    expr::pickle::Pickle pkl = d_sharedChannel->pop();

    Expr e = d_pickler.fromPickle(pkl);
    if(Trace.isOn("showSharing") && options::thread_id() == 0) {
      *options::out() << "thread #0: getNewLemma: " << e << endl;
    }
    return e;
  }

};/* class PortfolioLemmaInputChannel */



int runCvc4(int argc, char *argv[], Options& opts) {

#ifdef CVC4_CLN_IMP
  Warning() << "WARNING:" << endl
            << "WARNING: This build of portfolio-CVC4 uses the CLN library" << endl
            << "WARNING: which is not thread-safe!  Expect crashes and" << endl
            << "WARNING: incorrect answers." << endl
            << "WARNING:" << endl;
#endif /* CVC4_CLN_IMP */

  /**************************************************************************
   * runCvc4 outline:
   * -> Start a couple of timers
   * -> Processing of options, including thread specific ones
   * -> Statistics related stuff
   * -> Create ExprManager, parse commands, duplicate exprMgrs using export
   * -> Create smtEngines
   * -> Lemma sharing init
   * -> Run portfolio, exit/print stats etc.
   * (This list might become outdated, a timestamp might be good: 7 Dec '11.)
   **************************************************************************/

  // Timer statistic
  TimerStat s_totalTime("totalTime");
  TimerStat s_beforePortfolioTime("beforePortfolioTime");
  s_totalTime.start();
  s_beforePortfolioTime.start();

  // For the signal handlers' benefit
  pOptions = &opts;

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];


  /****************************** Options Processing ************************/

  // Parse the options
  int firstArgIndex = opts.parseOptions(argc, argv);

  progName = opts[options::binary_name].c_str();

  if( opts[options::help] ) {
    printUsage(opts, true);
    exit(1);
  } else if( opts[options::languageHelp] ) {
    Options::printLanguageHelp(*opts[options::out]);
    exit(1);
  } else if( opts[options::version] ) {
    *opts[options::out] << Configuration::about().c_str() << flush;
    exit(0);
  }

  unsigned numThreads = opts[options::threads];

  if(opts[options::threadArgv].size() > size_t(numThreads)) {
    stringstream ss;
    ss << "--thread" << (opts[options::threadArgv].size() - 1)
       << " configuration string seen but this portfolio will only contain "
       << numThreads << " thread(s)!";
    throw OptionException(ss.str());
  }

  segvNoSpin = opts[options::segvNoSpin];

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  *opts[options::out] << unitbuf;
#endif /* CVC4_COMPETITION_MODE */

  // We only accept one input file
  if(argc > firstArgIndex + 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin =
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!opts.wasSetByUser(options::interactive)) {
    opts.set(options::interactive, inputFromStdin && isatty(fileno(stdin)));
  }

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  if(opts[options::inputLanguage] == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      opts.set(options::inputLanguage, language::input::LANG_CVC4);
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V2);
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB);
      } else if((len >= 2 && !strcmp(".p", filename + len - 2))
                || (len >= 5 && !strcmp(".tptp", filename + len - 5))) {
        opts.set(options::inputLanguage, language::input::LANG_TPTP);
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        opts.set(options::inputLanguage, language::input::LANG_CVC4);
      }
    }
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    Debug.setStream(CVC4::null_os);
    Trace.setStream(CVC4::null_os);
    Notice.setStream(CVC4::null_os);
    Chat.setStream(CVC4::null_os);
    Message.setStream(CVC4::null_os);
    Warning.setStream(CVC4::null_os);
    Dump.setStream(CVC4::null_os);
  } else {
    if(opts[options::verbosity] < 2) {
      Chat.setStream(CVC4::null_os);
    }
    if(opts[options::verbosity] < 1) {
      Notice.setStream(CVC4::null_os);
    }
    if(opts[options::verbosity] < 0) {
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    }

    OutputLanguage language = language::toOutputLanguage(opts[options::inputLanguage]);
    Debug.getStream() << Expr::setlanguage(language);
    Trace.getStream() << Expr::setlanguage(language);
    Notice.getStream() << Expr::setlanguage(language);
    Chat.getStream() << Expr::setlanguage(language);
    Message.getStream() << Expr::setlanguage(language);
    Warning.getStream() << Expr::setlanguage(language);
    Dump.getStream() << Expr::setlanguage(language)
                     << Expr::setdepth(-1)
                     << Expr::printtypes(false);
  }

  // important even for muzzled builds (to get result output right)
  *opts[options::out] << Expr::setlanguage(opts[options::outputLanguage]);

  vector<Options> threadOptions;
  for(unsigned i = 0; i < numThreads; ++i) {
    threadOptions.push_back(opts);
    Options& tOpts = threadOptions.back();

    // Set thread identifier
    tOpts.set(options::thread_id, i);

    // If the random-seed is negative, pick a random seed randomly
    if(opts[options::satRandomSeed] < 0) {
      tOpts.set(options::satRandomSeed, (double)rand());
    }

    if(i < opts[options::threadArgv].size() && !opts[options::threadArgv][i].empty()) {
      // separate out the thread's individual configuration string
      stringstream optidss;
      optidss << "--thread" << i;
      string optid = optidss.str();
      int targc = 1;
      char* tbuf = strdup(opts[options::threadArgv][i].c_str());
      char* p = tbuf;
      // string length is certainly an upper bound on size needed
      char** targv = new char*[opts[options::threadArgv][i].size()];
      char** vp = targv;
      *vp++ = strdup(optid.c_str());
      p = strtok(p, " ");
      while(p != NULL) {
        *vp++ = p;
        ++targc;
        p = strtok(NULL, " ");
      }
      *vp++ = NULL;
      if(targc > 1) { // this is necessary in case you do e.g. --thread0="  "
        try {
          tOpts.parseOptions(targc, targv);
        } catch(OptionException& e) {
          stringstream ss;
          ss << optid << ": " << e.getMessage();
          throw OptionException(ss.str());
        }
        if(optind != targc) {
          stringstream ss;
          ss << "unused argument `" << targv[optind]
             << "' in thread configuration " << optid << " !";
          throw OptionException(ss.str());
        }
        if(tOpts[options::threads] != numThreads || tOpts[options::threadArgv] != opts[options::threadArgv]) {
          stringstream ss;
          ss << "not allowed to set thread options in " << optid << " !";
          throw OptionException(ss.str());
        }
      }
      free(targv[0]);
      delete targv;
      free(tbuf);
    }
  }

  // Some more options related stuff

  /* Use satRandomSeed for generating random numbers, in particular satRandomSeed-s */
  srand((unsigned int)(-opts[options::satRandomSeed]));

  assert(numThreads >= 1);      //do we need this?

  /* Output to string stream  */
  vector<stringstream*> ss_out(numThreads);
  if(opts[options::verbosity] == 0 || opts[options::separateOutput]) {
    for(unsigned i = 0; i < numThreads; ++i) {
      ss_out[i] = new stringstream;
      threadOptions[i].set(options::out, ss_out[i]);
    }
  }

  /****************************** Driver Statistics *************************/

  // Statistics init
  pStatistics = &theStatisticsRegistry;

  StatisticsRegistry driverStatisticsRegistry("driver");
  theStatisticsRegistry.registerStat_((&driverStatisticsRegistry));

  // Timer statistic
  RegisterStatistic* statTotalTime =
    new RegisterStatistic(&driverStatisticsRegistry, &s_totalTime);
  RegisterStatistic* statBeforePortfolioTime =
    new RegisterStatistic(&driverStatisticsRegistry, &s_beforePortfolioTime);

  // Filename statistics
  ReferenceStat< const char* > s_statFilename("filename", filename);
  RegisterStatistic* statFilenameReg =
    new RegisterStatistic(&driverStatisticsRegistry, &s_statFilename);


  /****************** ExprManager + CommandParsing + Export *****************/

  // Create the expression manager
  ExprManager* exprMgrs[numThreads];
  exprMgrs[0] = new ExprManager(threadOptions[0]);
  ExprManager* exprMgr = exprMgrs[0]; // to avoid having to change code which uses that

  // Parse commands until we are done
  Command* cmd;
  // bool status = true;           // Doesn't seem to be use right now: commenting it out
  CommandSequence* seq = new CommandSequence();
  if( opts[options::interactive] ) {
    InteractiveShell shell(*exprMgr, opts);
    Message() << Configuration::getPackageName()
              << " " << Configuration::getVersionString();
    if(Configuration::isSubversionBuild()) {
      Message() << " [subversion " << Configuration::getSubversionBranchName()
                << " r" << Configuration::getSubversionRevision()
                << (Configuration::hasSubversionModifications() ?
                    " (with modifications)" : "")
                << "]";
    }
    Message() << (Configuration::isDebugBuild() ? " DEBUG" : "")
              << " assertions:"
              << (Configuration::isAssertionBuild() ? "on" : "off")
              << endl;
    while((cmd = shell.readCommand())) {
      seq->addCommand(cmd);
    }
  } else {
    ParserBuilder parserBuilder =
      ParserBuilder(exprMgr, filename).
        withOptions(opts);

    if( inputFromStdin ) {
#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
      parserBuilder.withStreamInput(cin);
#else /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
      parserBuilder.withLineBufferedStreamInput(cin);
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
    }

    Parser *parser = parserBuilder.build();
    while((cmd = parser->nextCommand())) {
      seq->addCommand(cmd);
      // doCommand(smt, cmd, opts);
      // delete cmd;
    }
    // Remove the parser
    delete parser;
  }

  if(opts[options::parseOnly]) {
    return 0;
  }

  exprMgr = NULL;               // don't want to use that variable
                                // after this point

  /* Duplication, Individualisation */
  ExprManagerMapCollection* vmaps[numThreads]; // vmaps[0] is generally empty
  Command *seqs[numThreads];
  seqs[0] = seq;   seq = NULL;
  for(unsigned i = 1; i < numThreads; ++i) {
    vmaps[i] = new ExprManagerMapCollection();
    exprMgrs[i] = new ExprManager(threadOptions[i]);
    seqs[i] = seqs[0]->exportTo(exprMgrs[i], *(vmaps[i]) );
  }
  /**
   * vmaps[i].d_from [x] = y means
   *    that in thread #0's expr manager id is y
   *    and  in thread #i's expr manager id is x
   * opposite for d_to
   *
   * d_from[x] : in a sense gives the id if converting *from* it to
   *             first thread
   */

  /**
   * Create identity variable map for the first thread, with only
   * those variables which have a corresponding variable in another
   * thread. (TODO:Also assert, all threads have the same set of
   * variables mapped.)
   */
  if(numThreads >= 2) {
    // Get keys from the first thread
    //Set<uint64_t> s = vmaps[1]->d_to.keys();
    vmaps[0] = new ExprManagerMapCollection(); // identity be default?
    for(typeof(vmaps[1]->d_to.begin()) i=vmaps[1]->d_to.begin(); i!=vmaps[1]->d_to.end(); ++i) {
      (vmaps[0]->d_from)[i->first] = i->first;
    }
    vmaps[0]->d_to = vmaps[0]->d_from;
  }

  // Create the SmtEngine(s)
  SmtEngine *smts[numThreads];
  for(unsigned i = 0; i < numThreads; ++i) {
    smts[i] = new SmtEngine(exprMgrs[i]);

    // Register the statistics registry of the thread
    string emTag = "ExprManager thread #" + boost::lexical_cast<string>(threadOptions[i][options::thread_id]);
    string smtTag = "SmtEngine thread #" + boost::lexical_cast<string>(threadOptions[i][options::thread_id]);
    exprMgrs[i]->getStatisticsRegistry()->setName(emTag);
    smts[i]->getStatisticsRegistry()->setName(smtTag);
    theStatisticsRegistry.registerStat_( exprMgrs[i]->getStatisticsRegistry() );
    theStatisticsRegistry.registerStat_( smts[i]->getStatisticsRegistry() );
  }

  /************************* Lemma sharing init ************************/

  /* Sharing channels */
  SharedChannel<channelFormat> *channelsOut[numThreads], *channelsIn[numThreads];

  if(numThreads == 1) {
    // Disable sharing
    threadOptions[0].set(options::sharingFilterByLength, 0);
  } else {
    // Setup sharing channels
    const unsigned int sharingChannelSize = 1000000;

    for(unsigned i = 0; i < numThreads; ++i){
      if(Debug.isOn("channel-empty")) {
        channelsOut[i] = new EmptySharedChannel<channelFormat>(sharingChannelSize);
        channelsIn[i] = new EmptySharedChannel<channelFormat>(sharingChannelSize);
        continue;
      }
      channelsOut[i] = new SynchronizedSharedChannel<channelFormat>(sharingChannelSize);
      channelsIn[i] = new SynchronizedSharedChannel<channelFormat>(sharingChannelSize);
    }

    /* Lemma output channel */
    for(unsigned i = 0; i < numThreads; ++i) {
      string tag = "thread #" + boost::lexical_cast<string>(threadOptions[i][options::thread_id]);
      threadOptions[i].set(options::lemmaOutputChannel,
        new PortfolioLemmaOutputChannel(tag, channelsOut[i], exprMgrs[i],
                                        vmaps[i]->d_from, vmaps[i]->d_to));
      threadOptions[i].set(options::lemmaInputChannel,
        new PortfolioLemmaInputChannel(tag, channelsIn[i], exprMgrs[i],
                                       vmaps[i]->d_from, vmaps[i]->d_to));
    }
  }

  /************************** End of initialization ***********************/

  /* Portfolio */
  boost::function<Result()> fns[numThreads];

  for(unsigned i = 0; i < numThreads; ++i) {
    fns[i] = boost::bind(doSmt, boost::ref(*smts[i]), seqs[i], boost::ref(threadOptions[i]));
  }

  boost::function<void()>
    smFn = boost::bind(sharingManager<channelFormat>, numThreads, channelsOut, channelsIn, smts);

  s_beforePortfolioTime.stop();
  pair<int, Result> portfolioReturn = runPortfolio(numThreads, smFn, fns, true);
  int winner = portfolioReturn.first;
  Result result = portfolioReturn.second;

  cout << result << endl;

  /************************* Post printing answer ***********************/

  if(opts[options::printWinner]){
    cout << "The winner is #" << winner << endl;
  }

  Result satRes = result.asSatisfiabilityResult();
  int returnValue;
  if(satRes.isSat() == Result::SAT) {
    returnValue = 10;
  } else if(satRes.isSat() == Result::UNSAT) {
    returnValue = 20;
  } else {
    returnValue = 0;
  }

#ifdef CVC4_COMPETITION_MODE
  // exit, don't return
  // (don't want destructors to run)
  exit(returnValue);
#endif /* CVC4_COMPETITION_MODE */

  // ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  // RegisterStatistic statSatResultReg(*exprMgr, &s_statSatResult);

  // Stop timers, enough work done
  s_totalTime.stop();

  if(opts[options::statistics]) {
    pStatistics->flushInformation(*opts[options::err]);
  }

  if(opts[options::separateOutput]) {
    for(unsigned i = 0; i < numThreads; ++i) {
      *opts[options::out] << "--- Output from thread #" << i << " ---" << endl;
      *opts[options::out] << ss_out[i]->str();
    }
  }

  /*if(opts[options::statistics]) {
    double totalTime = double(s_totalTime.getData().tv_sec) +
        double(s_totalTime.getData().tv_nsec)/1000000000.0;
    cout.precision(6);
    *opts[options::err] << "real time: " << totalTime << "s\n";
    int th0_lemcnt = (*static_cast<PortfolioLemmaOutputChannel*>(opts[options::lemmaOutputChannel])).cnt;
    int th1_lemcnt = (*static_cast<PortfolioLemmaOutputChannel*>(threadOptions[1].lemmaOutputChannel)).cnt;
    *opts[options::err] << "lemmas shared by thread #0: " << th0_lemcnt << endl;
    *opts[options::err] << "lemmas shared by thread #1: " << th1_lemcnt << endl;
    *opts[options::err] << "sharing rate: " << double(th0_lemcnt+th1_lemcnt)/(totalTime)
                 << " lem/sec" << endl;
    *opts[options::err] << "winner: #" << (winner == 0 ? 0 : 1) << endl;
  }*/

  // destruction is causing segfaults, let us just exit
  exit(returnValue);

  //delete vmaps;

  delete statTotalTime;
  delete statBeforePortfolioTime;
  delete statFilenameReg;

  // delete seq;
  // delete exprMgr;

  // delete seq2;
  // delete exprMgr2;

  return returnValue;
}

/**** Code shared with driver.cpp ****/

namespace CVC4 {
  namespace main {/* Global options variable */
    CVC4_THREADLOCAL(Options*) pOptions;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;
  }
}

void printUsage(Options& opts, bool full) {
  stringstream ss;
  ss << "usage: " << opts[options::binary_name] << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  if(full) {
    Options::printUsage( ss.str(), *opts[options::out] );
  } else {
    Options::printShortUsage( ss.str(), *opts[options::out] );
  }
}

/** Executes a command. Deletes the command after execution. */
static bool doCommand(SmtEngine& smt, Command* cmd, Options& opts) {
  if( opts[options::parseOnly] ) {
    return true;
  }

  // assume no error
  bool status = true;

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      status = doCommand(smt, *subcmd, opts) && status;
    }
  } else {
    if(opts[options::verbosity] > 0) {
      *opts[options::out] << "Invoking: " << *cmd << endl;
    }

    if(opts[options::verbosity] >= 0) {
      cmd->invoke(&smt, *opts[options::out]);
    } else {
      cmd->invoke(&smt);
    }
    status = status && cmd->ok();
  }

  return status;
}

/**** End of code shared with driver.cpp ****/

/** Create the SMT engine and execute the commands */
Result doSmt(SmtEngine &smt, Command *cmd, Options &opts) {

  try {
    // For the signal handlers' benefit
    pOptions = &opts;

    // Execute the commands
    bool status = doCommand(smt, cmd, opts);

    // if(opts[options::statistics]) {
    //   smt.getStatisticsRegistry()->flushInformation(*opts[options::err]);
    //   *opts[options::err] << "Statistics printing of my thread complete " << endl;
    // }

    return status ? smt.getStatusOfLastCommand() : Result::SAT_UNKNOWN;
  } catch(OptionException& e) {
    *(*pOptions)[options::out] << "unknown" << endl;
    cerr << "CVC4 Error:" << endl << e << endl;
    printUsage(*pOptions);
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *(*pOptions)[options::out] << "unknown" << endl;
#endif
    *(*pOptions)[options::err] << "CVC4 Error:" << endl << e << endl;
    if((*pOptions)[options::statistics]) {
      pStatistics->flushInformation(*(*pOptions)[options::err]);
    }
  }
  return Result::SAT_UNKNOWN;
}

template<typename T>
void sharingManager(unsigned numThreads,
                    SharedChannel<T> *channelsOut[], // out and in with respect
                    SharedChannel<T> *channelsIn[],
                    SmtEngine *smts[])  // to smt engines
{
  Trace("sharing") << "sharing: thread started " << endl;
  vector <int> cnt(numThreads); // Debug("sharing")

  vector< queue<T> > queues;
  for(unsigned i = 0; i < numThreads; ++i){
    queues.push_back(queue<T>());
  }

  const unsigned int sharingBroadcastInterval = 1;

  boost::mutex mutex_activity;

  /* Disable interruption, so that we can check manually */
  boost::this_thread::disable_interruption di;

  while(not boost::this_thread::interruption_requested()) {

    boost::this_thread::sleep(boost::posix_time::milliseconds(sharingBroadcastInterval));

    for(unsigned t = 0; t < numThreads; ++t) {

      if(channelsOut[t]->empty()) continue;      /* No activity on this channel */

      /* Alert if channel full, so that we increase sharingChannelSize
         or decrease sharingBroadcastInterval */
      Assert(not channelsOut[t]->full());

      T data = channelsOut[t]->pop();

      if(Trace.isOn("sharing")) {
        ++cnt[t];
        Trace("sharing") << "sharing: Got data. Thread #" << t
                         << ". Chunk " << cnt[t] << std :: endl;
      }

      for(unsigned u = 0; u < numThreads; ++u) {
        if(u != t){
          Trace("sharing") << "sharing: adding to queue " << u << endl;
          queues[u].push(data);
        }
      }/* end of inner for: broadcast activity */

    } /* end of outer for: look for activity */

    for(unsigned t = 0; t < numThreads; ++t){
      /* Alert if channel full, so that we increase sharingChannelSize
         or decrease sharingBroadcastInterval */
      Assert(not channelsIn[t]->full());

      while(!queues[t].empty() && !channelsIn[t]->full()){
        Trace("sharing") << "sharing: pushing on channel " << t << endl;
        T data = queues[t].front();
        channelsIn[t]->push(data);
        queues[t].pop();
      }
    }
  } /* end of infinite while */

  Trace("interrupt") << "sharing thread interrupted, interrupting all smtEngines" << endl;

  for(unsigned t = 0; t < numThreads; ++t) {
    Trace("interrupt") << "Interrupting thread #" << t << endl;
    try{
      smts[t]->interrupt();
    }catch(ModalException &e){
      // It's fine, the thread is probably not there.
      Trace("interrupt") << "Could not interrupt thread #" << t << endl;
    }
  }

  Trace("sharing") << "sharing: Interrupted, exiting." << endl;
}
