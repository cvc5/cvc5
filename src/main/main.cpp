/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, cconway
 ** Minor contributors (to current version): barrett, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Main driver for CVC4 executable.
 **
 ** Main driver for CVC4 executable.
 **/

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <new>

#include <stdio.h>
#include <unistd.h>

#include "cvc4autoconfig.h"
#include "main.h"
#include "interactive_shell.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/Assert.h"
#include "util/configuration.h"
#include "util/options.h"
#include "util/output.h"
#include "util/result.h"
#include "util/stats.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

int runCvc4(int argc, char* argv[]);
void doCommand(SmtEngine&, Command*);
void printUsage();

namespace CVC4 {
  namespace main {/* Global options variable */
    Options options;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;
  }
}


// no more % chars in here without being escaped; it's used as a
// printf() format string
const string usageMessage = "\
usage: %s [options] [input-file]\n\
\n\
Without an input file, or with `-', CVC4 reads from standard input.\n\
\n\
CVC4 options:\n";

void printUsage() {
  stringstream ss;
  ss << "usage: " << options.binary_name << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  Options::printUsage( ss.str(), options.out );
}

/**
 * CVC4's main() routine is just an exception-safe wrapper around CVC4.
 * Please don't construct anything here.  Even if the constructor is
 * inside the try { }, an exception during destruction can cause
 * problems.  That's why main() wraps runCvc4() in the first place.
 * Put everything in runCvc4().
 */
int main(int argc, char* argv[]) {
  try {
    return runCvc4(argc, argv);
  } catch(OptionException& e) {
#ifdef CVC4_COMPETITION_MODE
    options.out << "unknown" << endl;
#endif
    cerr << "CVC4 Error:" << endl << e << endl;
    printUsage();
    exit(1);
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    options.out << "unknown" << endl;
#endif
    options.err << "CVC4 Error:" << endl << e << endl;
    if(options.statistics) {
      StatisticsRegistry::flushStatistics(options.err);
    }
    exit(1);
  } catch(bad_alloc) {
#ifdef CVC4_COMPETITION_MODE
    options.out << "unknown" << endl;
#endif
    options.err << "CVC4 ran out of memory." << endl;
    if(options.statistics) {
      StatisticsRegistry::flushStatistics(options.err);
    }
    exit(1);
  } catch(...) {
#ifdef CVC4_COMPETITION_MODE
    options.out << "unknown" << endl;
#endif
    options.err << "CVC4 threw an exception of unknown type." << endl;
    exit(1);
  }
}


int runCvc4(int argc, char* argv[]) {

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];
  
  // Parse the options
  int firstArgIndex = options.parseOptions(argc, argv);

  progName = options.binary_name.c_str();

  if( options.help ) {
    printUsage();
    exit(1);
  } else if( options.languageHelp ) {
    Options::printLanguageHelp(options.out);
    exit(1);
  } else if( options.version ) {
    options.out << Configuration::about().c_str() << flush;
    exit(0);
  } 

  segvNoSpin = options.segvNoSpin;

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  options.out << unitbuf;
#endif

  // We only accept one input file
  if(argc > firstArgIndex + 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin =
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!options.interactiveSetByUser) {
    options.interactive = inputFromStdin && isatty(fileno(stdin));
  }

  // Create the expression manager
  ExprManager exprMgr(options.earlyTypeChecking);

  // Create the SmtEngine
  SmtEngine smt(&exprMgr, options);

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  ReferenceStat< const char* > s_statFilename("filename", filename);
  StatisticsRegistry::registerStat(&s_statFilename);

  if(options.inputLanguage == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      options.inputLanguage = language::input::LANG_CVC4;
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        options.inputLanguage = language::input::LANG_SMTLIB_V2;
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        options.inputLanguage = language::input::LANG_SMTLIB;
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        options.inputLanguage = language::input::LANG_CVC4;
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
  } else {
    if(options.verbosity < 2) {
      Chat.setStream(CVC4::null_os);
    }
    if(options.verbosity < 1) {
      Notice.setStream(CVC4::null_os);
    }
    if(options.verbosity < 0) {
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    }

    OutputLanguage language = language::toOutputLanguage(options.inputLanguage);
    Debug.getStream() << Expr::setlanguage(language);
    Trace.getStream() << Expr::setlanguage(language);
    Notice.getStream() << Expr::setlanguage(language);
    Chat.getStream() << Expr::setlanguage(language);
    Message.getStream() << Expr::setlanguage(language);
    Warning.getStream() << Expr::setlanguage(language);
  }

  ParserBuilder parserBuilder =
      ParserBuilder(exprMgr, filename)
        .withInputLanguage(options.inputLanguage)
        .withMmap(options.memoryMap)
        .withChecks(options.semanticChecks &&
                    !Configuration::isMuzzledBuild() )
        .withStrictMode( options.strictParsing );

  if( inputFromStdin ) {
    parserBuilder.withStreamInput(cin);
  }

  // Parse and execute commands until we are done
  Command* cmd;
  if( options.interactive ) {
    InteractiveShell shell(options.in,options.out,parserBuilder);
    while((cmd = shell.readCommand())) {
      doCommand(smt,cmd);
      delete cmd;
    }
  } else {
    Parser *parser = parserBuilder.build();
    while((cmd = parser->nextCommand())) {
      doCommand(smt, cmd);
      delete cmd;
    }
    // Remove the parser
    delete parser;
  }

  string result = smt.getInfo(":status").getValue();
  int returnValue;

  if(result == "sat") {
    returnValue = 10;
  } else if(result == "unsat") {
    returnValue = 20;
  } else {
    returnValue = 0;
  }

#ifdef CVC4_COMPETITION_MODE
  // exit, don't return
  // (don't want destructors to run)
  exit(returnValue);
#endif

  ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  StatisticsRegistry::registerStat(&s_statSatResult);

  if(options.statistics) {
    StatisticsRegistry::flushStatistics(options.err);
  }

  StatisticsRegistry::unregisterStat(&s_statSatResult);
  StatisticsRegistry::unregisterStat(&s_statFilename);

  return returnValue;
}

/** Executes a command. Deletes the command after execution. */
void doCommand(SmtEngine& smt, Command* cmd) {
  if( options.parseOnly ) {
    return;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      doCommand(smt, *subcmd);
    }
  } else {
    if(options.verbosity > 0) {
      options.out << "Invoking: " << *cmd << endl;
    }

    if(options.verbosity >= 0) {
      cmd->invoke(&smt, options.out);
    } else {
      cmd->invoke(&smt);
    }
  }
}
