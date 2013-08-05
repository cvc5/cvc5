/*********************                                                        */
/*! \file driver_unified.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Driver for CVC4 executable (cvc4) unified for both
 ** sequential and portfolio versions
 **/

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <new>
#include <unistd.h>

#include <stdio.h>
#include <unistd.h>

#include "cvc4autoconfig.h"
#include "main/main.h"
#include "main/interactive_shell.h"
#include "main/options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "expr/command.h"
#include "util/configuration.h"
#include "options/options.h"
#include "main/command_executor.h"
# ifdef PORTFOLIO_BUILD
#    include "main/command_executor_portfolio.h"
# endif
#include "main/options.h"
#include "smt/options.h"
#include "theory/uf/options.h"
#include "util/output.h"
#include "util/dump.h"
#include "util/result.h"
#include "util/statistics_registry.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

namespace CVC4 {
  namespace main {
    /** Global options variable */
    CVC4_THREADLOCAL(Options*) pOptions;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;

    /** A pointer to the CommandExecutor (the signal handlers need it) */
    CVC4::main::CommandExecutor* pExecutor = NULL;

    /** A pointer to the totalTime driver stat (the signal handlers need it) */
    CVC4::TimerStat* pTotalTime = NULL;

  }/* CVC4::main namespace */
}/* CVC4 namespace */


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

int runCvc4(int argc, char* argv[], Options& opts) {

  // Timer statistic
  pTotalTime = new TimerStat("totalTime");
  pTotalTime->start();

  // For the signal handlers' benefit
  pOptions = &opts;

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];

  // Parse the options
  vector<string> filenames = opts.parseOptions(argc, argv);

# ifndef PORTFOLIO_BUILD
  if( opts.wasSetByUser(options::threads) ||
      ! opts[options::threadArgv].empty() ) {
    throw OptionException("Thread options cannot be used with sequential CVC4.  Please build and use the portfolio binary `pcvc4'.");
  }
# else
  if( opts[options::checkProofs] ) {
    throw OptionException("Cannot run portfolio in check-proofs mode.");
  }
# endif

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

  segvSpin = opts[options::segvSpin];

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  *opts[options::out] << unitbuf;
#endif /* CVC4_COMPETITION_MODE */

  // We only accept one input file
  if(filenames.size() > 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin = filenames.empty() || filenames[0] == "-";

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!opts.wasSetByUser(options::interactive)) {
    opts.set(options::interactive, inputFromStdin && isatty(fileno(stdin)));
  }

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : filenames[0].c_str();

  if(opts[options::inputLanguage] == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      opts.set(options::inputLanguage, language::input::LANG_CVC4);
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V2);
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V1);
      } else if(len >= 5 && !strcmp(".smt1", filename + len - 5)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V1);
      } else if((len >= 2 && !strcmp(".p", filename + len - 2))
                || (len >= 5 && !strcmp(".tptp", filename + len - 5))) {
        opts.set(options::inputLanguage, language::input::LANG_TPTP);
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        opts.set(options::inputLanguage, language::input::LANG_CVC4);
      }
    }
  }

  if(opts[options::outputLanguage] == language::output::LANG_AUTO) {
    opts.set(options::outputLanguage, language::toOutputLanguage(opts[options::inputLanguage]));
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(CVC4::null_os);
    TraceChannel.setStream(CVC4::null_os);
    NoticeChannel.setStream(CVC4::null_os);
    ChatChannel.setStream(CVC4::null_os);
    MessageChannel.setStream(CVC4::null_os);
    WarningChannel.setStream(CVC4::null_os);
    DumpChannel.setStream(CVC4::null_os);
  }

  // important even for muzzled builds (to get result output right)
  *opts[options::out] << Expr::setlanguage(opts[options::outputLanguage]);
  DumpChannel.getStream() << Expr::setlanguage(opts[options::outputLanguage]);

  // Create the expression manager using appropriate options
  ExprManager* exprMgr;
# ifndef PORTFOLIO_BUILD
  exprMgr = new ExprManager(opts);
  pExecutor = new CommandExecutor(*exprMgr, opts);
# else
  vector<Options> threadOpts = parseThreadSpecificOptions(opts);
  if(opts.wasSetByUser(options::incrementalSolving) &&
     opts[options::incrementalSolving] &&
     !opts[options::incrementalParallel]) {
    Notice() << "Notice: In --incremental mode, using the sequential solver unless forced by...\n"
             << "Notice: ...the experimental --incremental-parallel option.\n";
    exprMgr = new ExprManager(opts);
    pExecutor = new CommandExecutor(*exprMgr, opts);
  } else {
    exprMgr = new ExprManager(threadOpts[0]);
    pExecutor = new CommandExecutorPortfolio(*exprMgr, opts, threadOpts);
  }
# endif

  Parser* replayParser = NULL;
  if( opts[options::replayFilename] != "" ) {
    ParserBuilder replayParserBuilder(exprMgr, opts[options::replayFilename], opts);

    if( opts[options::replayFilename] == "-") {
      if( inputFromStdin ) {
        throw OptionException("Replay file and input file can't both be stdin.");
      }
      replayParserBuilder.withStreamInput(cin);
    }
    replayParser = replayParserBuilder.build();
    opts.set(options::replayStream, new Parser::ExprStream(replayParser));
  }
  if( opts[options::replayLog] != NULL ) {
    *opts[options::replayLog] << Expr::setlanguage(opts[options::outputLanguage]) << Expr::setdepth(-1);
  }

  int returnValue = 0;
  {
    // Timer statistic
    RegisterStatistic statTotalTime(&pExecutor->getStatisticsRegistry(), pTotalTime);

    // Filename statistics
    ReferenceStat< const char* > s_statFilename("filename", filename);
    RegisterStatistic statFilenameReg(&pExecutor->getStatisticsRegistry(), &s_statFilename);

    // Parse and execute commands until we are done
    Command* cmd;
    bool status = true;
    if(opts[options::interactive] && inputFromStdin) {
#ifndef PORTFOLIO_BUILD
      if(!opts.wasSetByUser(options::incrementalSolving)) {
        cmd = new SetOptionCommand("incremental", true);
        pExecutor->doCommand(cmd);
        delete cmd;
      }
#endif /* PORTFOLIO_BUILD */
      InteractiveShell shell(*exprMgr, opts);
      Message() << Configuration::getPackageName()
                << " " << Configuration::getVersionString();
      if(Configuration::isGitBuild()) {
        Message() << " [" << Configuration::getGitId() << "]";
      } else if(Configuration::isSubversionBuild()) {
        Message() << " [" << Configuration::getSubversionId() << "]";
      }
      Message() << (Configuration::isDebugBuild() ? " DEBUG" : "")
                << " assertions:"
                << (Configuration::isAssertionBuild() ? "on" : "off")
                << endl;
      if(replayParser != NULL) {
        // have the replay parser use the declarations input interactively
        replayParser->useDeclarationsFrom(shell.getParser());
      }
      while((cmd = shell.readCommand())) {
        status = pExecutor->doCommand(cmd) && status;
        delete cmd;
      }
    } else {
      if(!opts.wasSetByUser(options::incrementalSolving)) {
        cmd = new SetOptionCommand("incremental", false);
        pExecutor->doCommand(cmd);
        delete cmd;
      }

      ParserBuilder parserBuilder(exprMgr, filename, opts);

      if( inputFromStdin ) {
#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
        parserBuilder.withStreamInput(cin);
#else /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
        parserBuilder.withLineBufferedStreamInput(cin);
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
      }

      Parser *parser = parserBuilder.build();
      if(replayParser != NULL) {
        // have the replay parser use the file's declarations
        replayParser->useDeclarationsFrom(parser);
      }
      while(status && (cmd = parser->nextCommand())) {
        if(dynamic_cast<QuitCommand*>(cmd) != NULL) {
          delete cmd;
          break;
        }
        status = pExecutor->doCommand(cmd);
        delete cmd;
      }
      // Remove the parser
      delete parser;
    }

    if( opts[options::replayStream] != NULL ) {
      // this deletes the expression parser too
      delete opts[options::replayStream];
      opts.set(options::replayStream, NULL);
    }

    Result result;
    if(status) {
      result = pExecutor->getResult();
      returnValue = 0;
    } else {
      // there was some kind of error
      returnValue = 1;
    }

#ifdef CVC4_COMPETITION_MODE
    // exit, don't return (don't want destructors to run)
    // _exit() from unistd.h doesn't run global destructors
    // or other on_exit/atexit stuff.
    _exit(returnValue);
#endif /* CVC4_COMPETITION_MODE */

    ReferenceStat< Result > s_statSatResult("sat/unsat", result);
    RegisterStatistic statSatResultReg(&pExecutor->getStatisticsRegistry(), &s_statSatResult);

    pTotalTime->stop();

    // Set the global executor pointer to NULL first.  If we get a
    // signal while dumping statistics, we don't want to try again.
    if(opts[options::statistics]) {
      pExecutor->flushStatistics(*opts[options::err]);
    }

    // make sure to flush replay output log before early-exit
    if( opts[options::replayLog] != NULL ) {
      *opts[options::replayLog] << flush;
    }

    // make sure out and err streams are flushed too
    *opts[options::out] << flush;
    *opts[options::err] << flush;
 
#ifdef CVC4_DEBUG
    if(opts[options::earlyExit] && opts.wasSetByUser(options::earlyExit)) {
      _exit(returnValue);
    }
#else /* CVC4_DEBUG */
    if(opts[options::earlyExit]) {
      _exit(returnValue);
    }
#endif /* CVC4_DEBUG */
  }

  // On exceptional exit, these are leaked, but that's okay... they
  // need to be around in that case for main() to print statistics.
  delete pTotalTime;
  delete pExecutor;
  delete exprMgr;

  pTotalTime = NULL;
  pExecutor = NULL;

  return returnValue;
}
