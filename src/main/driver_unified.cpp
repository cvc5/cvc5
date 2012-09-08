/*********************                                                        */
/*! \file driver_unified.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): barrett, dejan, taking, kshitij
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011, 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

#include <stdio.h>
#include <unistd.h>

#include "cvc4autoconfig.h"
#include "main/main.h"
#include "main/interactive_shell.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "expr/command.h"
#include "util/Assert.h"
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
#include "util/stats.h"

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

    /** A pointer to the StatisticsRegistry (the signal handlers need it) */
    CVC4::StatisticsRegistry* pStatistics;
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

int runCvc4(int argc, char* argv[], Options& opts) {

  // Timer statistic
  TimerStat s_totalTime("totalTime");
  s_totalTime.start();

  // For the signal handlers' benefit
  pOptions = &opts;

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];

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

  if(opts[options::outputLanguage] == language::output::LANG_AUTO) {
    opts.set(options::outputLanguage, language::toOutputLanguage(opts[options::inputLanguage]));
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

    Debug.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Trace.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Notice.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Chat.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Message.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Warning.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Dump.getStream() << Expr::setlanguage(opts[options::outputLanguage])
                     << Expr::setdepth(-1)
                     << Expr::printtypes(false);
  }

  // important even for muzzled builds (to get result output right)
  *opts[options::out] << Expr::setlanguage(opts[options::outputLanguage]);

  // Create the expression manager using appropriate options
# ifndef PORTFOLIO_BUILD
  ExprManager exprMgr(opts);
# else
  vector<Options> threadOpts   = parseThreadSpecificOptions(opts);
  ExprManager exprMgr(threadOpts[0]);
# endif

  CommandExecutor* cmdExecutor = 
# ifndef PORTFOLIO_BUILD
    new CommandExecutor(exprMgr, opts);
# else
    new CommandExecutorPortfolio(exprMgr, opts, threadOpts);
#endif

  // Create the SmtEngine
  StatisticsRegistry driverStats("driver");
  pStatistics->registerStat_(&driverStats);

  Parser* replayParser = NULL;
  if( opts[options::replayFilename] != "" ) {
    ParserBuilder replayParserBuilder(&exprMgr, opts[options::replayFilename], opts);

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

  // Timer statistic
  RegisterStatistic statTotalTime(&driverStats, &s_totalTime);

  // Filename statistics
  ReferenceStat< const char* > s_statFilename("filename", filename);
  RegisterStatistic statFilenameReg(&driverStats, &s_statFilename);

  // Parse and execute commands until we are done
  Command* cmd;
  bool status = true;
  if( opts[options::interactive] ) {
    InteractiveShell shell(exprMgr, opts);
    Message() << Configuration::getPackageName()
              << " " << Configuration::getVersionString();
    if(Configuration::isSubversionBuild()) {
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
      status = cmdExecutor->doCommand(cmd) && status;
      delete cmd;
    }
  } else {
    ParserBuilder parserBuilder(&exprMgr, filename, opts);

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
      status = cmdExecutor->doCommand(cmd);
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

  int returnValue;
  string result = "unknown";
  if(status) {
    result = cmdExecutor->getSmtEngineStatus();

    if(result == "sat") {
      returnValue = 10;
    } else if(result == "unsat") {
      returnValue = 20;
    } else {
      returnValue = 0;
    }
  } else {
    // there was some kind of error
    returnValue = 1;
  }

#ifdef CVC4_COMPETITION_MODE
  // exit, don't return
  // (don't want destructors to run)
  exit(returnValue);
#endif /* CVC4_COMPETITION_MODE */

  ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  RegisterStatistic statSatResultReg(&driverStats, &s_statSatResult);

  s_totalTime.stop();

  if(opts[options::statistics]) {
    pStatistics->flushInformation(*opts[options::err]);
  }
  exit(returnValue);
  return returnValue;
}
