/*********************                                                        */
/*! \file driver_unified.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Driver for CVC4 executable (cvc4) unified for both
 ** sequential and portfolio versions
 **/

#include <stdio.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <new>

#include "base/output.h"
#include "cvc4autoconfig.h"
#include "expr/expr_manager.h"
#include "expr/result.h"
#include "expr/statistics_registry.h"
#include "main/command_executor.h"

#ifdef PORTFOLIO_BUILD
#  include "main/command_executor_portfolio.h"
#endif

#include "main/interactive_shell.h"
#include "main/main.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/quantifiers_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "smt/smt_options_handler.h"
#include "smt_util/command.h"
#include "util/configuration.h"

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

void printStatsFilterZeros(std::ostream& out, const std::string& statsString) {
  // read each line, if a number, check zero and skip if so
  // Stat are assumed to one-per line: "<statName>, <statValue>"

  std::istringstream iss(statsString);
  std::string statName, statValue;

  std::getline(iss, statName, ',');

  while( !iss.eof() ) {

    std::getline(iss, statValue, '\n');

    double curFloat;
    bool isFloat = (std::istringstream(statValue) >> curFloat);

    if( (isFloat && curFloat == 0) ||
        statValue == " \"0\"" ||
        statValue == " \"[]\"") {
      // skip
    } else {
      out << statName << "," << statValue << std::endl;
    }

    std::getline(iss, statName, ',');
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

#warning "TODO: Check that the SmtEngine pointer should be NULL with Kshitij."
  smt::SmtOptionsHandler optionsHandler(NULL);

  // Parse the options
  vector<string> filenames = opts.parseOptions(argc, argv, &optionsHandler);

# ifndef PORTFOLIO_BUILD
  if( opts.wasSetByUser(options::threads) ||
      opts.wasSetByUser(options::threadStackSize) ||
      ! opts[options::threadArgv].empty() ) {
    throw OptionException("Thread options cannot be used with sequential CVC4.  Please build and use the portfolio binary `pcvc4'.");
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
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V2_0);
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
      } else if((len >= 3 && !strcmp(".sy", filename + len - 3))
                || (len >= 3 && !strcmp(".sl", filename + len - 3))) {
        opts.set(options::inputLanguage, language::input::LANG_SYGUS);
        //since there is no sygus output language, set this to SMT lib 2
        //opts.set(options::outputLanguage, language::output::LANG_SMTLIB_V2_0);
      }
    }
  }

  if(opts[options::outputLanguage] == language::output::LANG_AUTO) {
    opts.set(options::outputLanguage, language::toOutputLanguage(opts[options::inputLanguage]));
  }

  // if doing sygus, turn on CEGQI by default
  if(opts[options::inputLanguage] == language::input::LANG_SYGUS ){
    if( !opts.wasSetByUser(options::ceGuidedInst)) {
      opts.set(options::ceGuidedInst, true);
    }
    if( !opts.wasSetByUser(options::dumpSynth)) {
      opts.set(options::dumpSynth, true);
    }
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(CVC4::null_os);
    TraceChannel.setStream(CVC4::null_os);
    NoticeChannel.setStream(CVC4::null_os);
    ChatChannel.setStream(CVC4::null_os);
    MessageChannel.setStream(CVC4::null_os);
    WarningChannel.setStream(CVC4::null_os);
  }

  // important even for muzzled builds (to get result output right)
  *opts[options::out] << language::SetLanguage(opts[options::outputLanguage]);

  // Create the expression manager using appropriate options
  ExprManager* exprMgr;
# ifndef PORTFOLIO_BUILD
  exprMgr = new ExprManager(opts);
  pExecutor = new CommandExecutor(*exprMgr, opts);
# else
  vector<Options> threadOpts = parseThreadSpecificOptions(opts);
  bool useParallelExecutor = true;
  // incremental?
  if(opts.wasSetByUser(options::incrementalSolving) &&
     opts[options::incrementalSolving] &&
     !opts[options::incrementalParallel]) {
    Notice() << "Notice: In --incremental mode, using the sequential solver unless forced by...\n"
             << "Notice: ...the experimental --incremental-parallel option.\n";
    useParallelExecutor = false;
  }
  // proofs?
  if(opts[options::checkProofs]) {
    if(opts[options::fallbackSequential]) {
      Warning() << "Warning: Falling back to sequential mode, as cannot run portfolio in check-proofs mode.\n";
      useParallelExecutor = false;
    }
    else {
      throw OptionException("Cannot run portfolio in check-proofs mode.");
    }
  }
  // pick appropriate one
  if(useParallelExecutor) {
    exprMgr = new ExprManager(threadOpts[0]);
    pExecutor = new CommandExecutorPortfolio(*exprMgr, opts, threadOpts);
  } else {
    exprMgr = new ExprManager(opts);
    pExecutor = new CommandExecutor(*exprMgr, opts);
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
    *opts[options::replayLog] << language::SetLanguage(opts[options::outputLanguage]) << Expr::setdepth(-1);
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
      if(opts[options::tearDownIncremental]) {
        throw OptionException("--tear-down-incremental doesn't work in interactive mode");
      }
#ifndef PORTFOLIO_BUILD
      if(!opts.wasSetByUser(options::incrementalSolving)) {
        cmd = new SetOptionCommand("incremental", SExpr(true));
        cmd->setMuted(true);
        pExecutor->doCommand(cmd);
        delete cmd;
      }
#endif /* PORTFOLIO_BUILD */
      InteractiveShell shell(*exprMgr, opts);
      if(opts[options::interactivePrompt]) {
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
      }
      if(replayParser != NULL) {
        // have the replay parser use the declarations input interactively
        replayParser->useDeclarationsFrom(shell.getParser());
      }

      while(true) {
        try {
          cmd = shell.readCommand();
        } catch(UnsafeInterruptException& e) {
          *opts[options::out] << CommandInterrupted();
          break;
        }
        if (cmd == NULL)
          break;
        status = pExecutor->doCommand(cmd) && status;
        if (cmd->interrupted()) {
          delete cmd;
          break;
        }
        delete cmd;
      }
    } else if(opts[options::tearDownIncremental]) {
      if(opts[options::incrementalSolving]) {
        if(opts.wasSetByUser(options::incrementalSolving)) {
          throw OptionException("--tear-down-incremental incompatible with --incremental");
        }

        cmd = new SetOptionCommand("incremental", SExpr(false));
        cmd->setMuted(true);
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

      vector< vector<Command*> > allCommands;
      allCommands.push_back(vector<Command*>());
      Parser *parser = parserBuilder.build();
      if(replayParser != NULL) {
        // have the replay parser use the file's declarations
        replayParser->useDeclarationsFrom(parser);
      }
      bool needReset = false;
      // true if one of the commands was interrupted
      bool interrupted = false;
      while (status || opts[options::continuedExecution]) {
        if (interrupted) {
          *opts[options::out] << CommandInterrupted();
          break;
        }

        try {
          cmd = parser->nextCommand();
          if (cmd == NULL) break;
        } catch (UnsafeInterruptException& e) {
          interrupted = true;
          continue;
        }

        if(dynamic_cast<PushCommand*>(cmd) != NULL) {
          if(needReset) {
            pExecutor->reset();
            for(size_t i = 0; i < allCommands.size() && !interrupted; ++i) {
              if (interrupted) break;
              for(size_t j = 0; j < allCommands[i].size() && !interrupted; ++j) {
                Command* cmd = allCommands[i][j]->clone();
                cmd->setMuted(true);
                pExecutor->doCommand(cmd);
                if(cmd->interrupted()) {
                  interrupted = true;
                }
                delete cmd;
              }
            }
            needReset = false;
          }
          *opts[options::out] << CommandSuccess();
          allCommands.push_back(vector<Command*>());
        } else if(dynamic_cast<PopCommand*>(cmd) != NULL) {
          allCommands.pop_back(); // fixme leaks cmds here
          pExecutor->reset();
          for(size_t i = 0; i < allCommands.size() && !interrupted; ++i) {
            for(size_t j = 0; j < allCommands[i].size() && !interrupted; ++j) {
              Command* cmd = allCommands[i][j]->clone();
              cmd->setMuted(true);
              pExecutor->doCommand(cmd);
              if(cmd->interrupted()) {
                interrupted = true;
              }
              delete cmd;
            }
          }
          if (interrupted) continue;
          *opts[options::out] << CommandSuccess();
        } else if(dynamic_cast<CheckSatCommand*>(cmd) != NULL ||
                  dynamic_cast<QueryCommand*>(cmd) != NULL) {
          if(needReset) {
            pExecutor->reset();
            for(size_t i = 0; i < allCommands.size() && !interrupted; ++i) {
              for(size_t j = 0; j < allCommands[i].size() && !interrupted; ++j) {
                Command* cmd = allCommands[i][j]->clone();
                cmd->setMuted(true);
                pExecutor->doCommand(cmd);
                if(cmd->interrupted()) {
                  interrupted = true;
                }
                delete cmd;
              }
            }
          }
          if (interrupted) {
            continue;
          }

          status = pExecutor->doCommand(cmd);
          if(cmd->interrupted()) {
            interrupted = true;
            continue;
          }
          needReset = true;
        } else if(dynamic_cast<ResetCommand*>(cmd) != NULL) {
          pExecutor->doCommand(cmd);
          allCommands.clear();
          allCommands.push_back(vector<Command*>());
        } else {
          // We shouldn't copy certain commands, because they can cause
          // an error on replay since there's no associated sat/unsat check
          // preceding them.
          if(dynamic_cast<GetUnsatCoreCommand*>(cmd) == NULL &&
             dynamic_cast<GetProofCommand*>(cmd) == NULL &&
             dynamic_cast<GetValueCommand*>(cmd) == NULL &&
             dynamic_cast<GetModelCommand*>(cmd) == NULL &&
             dynamic_cast<GetAssignmentCommand*>(cmd) == NULL &&
             dynamic_cast<GetInstantiationsCommand*>(cmd) == NULL &&
             dynamic_cast<GetAssertionsCommand*>(cmd) == NULL &&
             dynamic_cast<GetInfoCommand*>(cmd) == NULL &&
             dynamic_cast<GetOptionCommand*>(cmd) == NULL &&
             dynamic_cast<EchoCommand*>(cmd) == NULL) {
            Command* copy = cmd->clone();
            allCommands.back().push_back(copy);
          }
          status = pExecutor->doCommand(cmd);
          if(cmd->interrupted()) {
            interrupted = true;
            continue;
          }

          if(dynamic_cast<QuitCommand*>(cmd) != NULL) {
            delete cmd;
            break;
          }
        }
        delete cmd;
      }
      // Remove the parser
      delete parser;
    } else {
      if(!opts.wasSetByUser(options::incrementalSolving)) {
        cmd = new SetOptionCommand("incremental", SExpr(false));
        cmd->setMuted(true);
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
      bool interrupted = false;
      while(status || opts[options::continuedExecution]) {
        if (interrupted) {
          *opts[options::out] << CommandInterrupted();
          pExecutor->reset();
          break;
        }
        try {
          cmd = parser->nextCommand();
          if (cmd == NULL) break;
        } catch (UnsafeInterruptException& e) {
          interrupted = true;
          continue;
        }

        status = pExecutor->doCommand(cmd);
        if (cmd->interrupted() && status == 0) {
          interrupted = true;
          break;
        }

        if(dynamic_cast<QuitCommand*>(cmd) != NULL) {
          delete cmd;
          break;
        }
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
    *opts[options::out] << flush;
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
      if(opts[options::statsHideZeros] == false) {
        pExecutor->flushStatistics(*opts[options::err]);
      } else {
        std::ostringstream ossStats;
        pExecutor->flushStatistics(ossStats);
        printStatsFilterZeros(*opts[options::err], ossStats.str());
      }
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

  cvc4_shutdown();

  return returnValue;
}
