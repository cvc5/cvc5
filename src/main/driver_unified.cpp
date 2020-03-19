/*********************                                                        */
/*! \file driver_unified.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Driver for CVC4 executable (cvc4)
 **/

#include <stdio.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <new>

#include "cvc4autoconfig.h"

#include "api/cvc4cpp.h"
#include "base/configuration.h"
#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "expr/expr_manager.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "main/main.h"
#include "options/options.h"
#include "options/set_language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "smt/command.h"
#include "util/result.h"
#include "util/statistics_registry.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

namespace CVC4 {
  namespace main {
    /** Global options variable */
    thread_local Options* pOptions;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const std::string *progName;

    /** A pointer to the CommandExecutor (the signal handlers need it) */
    CVC4::main::CommandExecutor* pExecutor = NULL;

    /** A pointer to the totalTime driver stat (the signal handlers need it) */
    CVC4::TimerStat* pTotalTime = NULL;

  }/* CVC4::main namespace */
}/* CVC4 namespace */


void printUsage(Options& opts, bool full) {
  stringstream ss;
  ss << "usage: " << opts.getBinaryName() << " [options] [input-file]"
     << endl << endl
     << "Without an input file, or with `-', CVC4 reads from standard input."
     << endl << endl
     << "CVC4 options:" << endl;
  if(full) {
    Options::printUsage( ss.str(), *(opts.getOut()) );
  } else {
    Options::printShortUsage( ss.str(), *(opts.getOut()) );
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
  vector<string> filenames = Options::parseOptions(&opts, argc, argv);

  string progNameStr = opts.getBinaryName();
  progName = &progNameStr;

  if( opts.getHelp() ) {
    printUsage(opts, true);
    exit(1);
  } else if( opts.getLanguageHelp() ) {
    Options::printLanguageHelp(*(opts.getOut()));
    exit(1);
  } else if( opts.getVersion() ) {
    *(opts.getOut()) << Configuration::about().c_str() << flush;
    exit(0);
  }

  segvSpin = opts.getSegvSpin();

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  *(opts.getOut()) << unitbuf;
#endif /* CVC4_COMPETITION_MODE */

  // We only accept one input file
  if(filenames.size() > 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin = filenames.empty() || filenames[0] == "-";

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!opts.wasSetByUserInteractive()) {
    opts.setInteractive(inputFromStdin && isatty(fileno(stdin)));
  }

  // Auto-detect input language by filename extension
  std::string filenameStr("<stdin>");
  if (!inputFromStdin) {
    // Use swap to avoid copying the string
    // TODO: use std::move() when switching to c++11
    filenameStr.swap(filenames[0]);
  }
  const char* filename = filenameStr.c_str();

  if(opts.getInputLanguage() == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      opts.setInputLanguage(language::input::LANG_CVC4);
    } else {
      unsigned len = filenameStr.size();
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        opts.setInputLanguage(language::input::LANG_SMTLIB_V2_6);
      } else if((len >= 2 && !strcmp(".p", filename + len - 2))
                || (len >= 5 && !strcmp(".tptp", filename + len - 5))) {
        opts.setInputLanguage(language::input::LANG_TPTP);
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        opts.setInputLanguage(language::input::LANG_CVC4);
      } else if((len >= 3 && !strcmp(".sy", filename + len - 3))
                || (len >= 3 && !strcmp(".sl", filename + len - 3))) {
        opts.setInputLanguage(language::input::LANG_SYGUS);
        //since there is no sygus output language, set this to SMT lib 2
        //opts.setOutputLanguage(language::output::LANG_SMTLIB_V2_0);
      }
    }
  }

  if(opts.getOutputLanguage() == language::output::LANG_AUTO) {
    opts.setOutputLanguage(language::toOutputLanguage(opts.getInputLanguage()));
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(&CVC4::null_os);
    TraceChannel.setStream(&CVC4::null_os);
    NoticeChannel.setStream(&CVC4::null_os);
    ChatChannel.setStream(&CVC4::null_os);
    MessageChannel.setStream(&CVC4::null_os);
    WarningChannel.setStream(&CVC4::null_os);
  }

  // important even for muzzled builds (to get result output right)
  (*(opts.getOut())) << language::SetLanguage(opts.getOutputLanguage());

  // Create the command executor to execute the parsed commands
  pExecutor = new CommandExecutor(opts);

  std::unique_ptr<Parser> replayParser;
  if (opts.getReplayInputFilename() != "")
  {
    std::string replayFilename = opts.getReplayInputFilename();
    ParserBuilder replayParserBuilder(
        pExecutor->getSolver(), replayFilename, opts);

    if( replayFilename == "-") {
      if( inputFromStdin ) {
        throw OptionException("Replay file and input file can't both be stdin.");
      }
      replayParserBuilder.withStreamInput(cin);
    }
    replayParser.reset(replayParserBuilder.build());
    pExecutor->setReplayStream(new Parser::ExprStream(replayParser.get()));
  }

  int returnValue = 0;
  {
    // Timer statistic
    RegisterStatistic statTotalTime(&pExecutor->getStatisticsRegistry(),
                                    pTotalTime);

    // Filename statistics
    ReferenceStat<std::string> s_statFilename("filename", filenameStr);
    RegisterStatistic statFilenameReg(&pExecutor->getStatisticsRegistry(),
                                      &s_statFilename);
    // set filename in smt engine
    pExecutor->getSmtEngine()->setFilename(filenameStr);

    // Parse and execute commands until we are done
    Command* cmd;
    bool status = true;
    if(opts.getInteractive() && inputFromStdin) {
      if(opts.getTearDownIncremental() > 0) {
        throw OptionException(
            "--tear-down-incremental doesn't work in interactive mode");
      }
      if(!opts.wasSetByUserIncrementalSolving()) {
        cmd = new SetOptionCommand("incremental", SExpr(true));
        cmd->setMuted(true);
        pExecutor->doCommand(cmd);
        delete cmd;
      }
      InteractiveShell shell(pExecutor->getSolver());
      if(opts.getInteractivePrompt()) {
        Message() << Configuration::getPackageName()
                  << " " << Configuration::getVersionString();
        if(Configuration::isGitBuild()) {
          Message() << " [" << Configuration::getGitId() << "]";
        }
        Message() << (Configuration::isDebugBuild() ? " DEBUG" : "")
                  << " assertions:"
                  << (Configuration::isAssertionBuild() ? "on" : "off")
                  << endl << endl;
        Message() << Configuration::copyright() << endl;
      }
      if(replayParser) {
        // have the replay parser use the declarations input interactively
        replayParser->useDeclarationsFrom(shell.getParser());
      }

      while(true) {
        try {
          cmd = shell.readCommand();
        } catch(UnsafeInterruptException& e) {
          (*opts.getOut()) << CommandInterrupted();
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
    } else if( opts.getTearDownIncremental() > 0) {
      if(!opts.getIncrementalSolving() && opts.getTearDownIncremental() > 1) {
        // For tear-down-incremental values greater than 1, need incremental
        // on too.
        cmd = new SetOptionCommand("incremental", SExpr(true));
        cmd->setMuted(true);
        pExecutor->doCommand(cmd);
        delete cmd;
        // if(opts.wasSetByUserIncrementalSolving()) {
        //   throw OptionException(
        //     "--tear-down-incremental incompatible with --incremental");
        // }

        // cmd = new SetOptionCommand("incremental", SExpr(false));
        // cmd->setMuted(true);
        // pExecutor->doCommand(cmd);
        // delete cmd;
      }

      ParserBuilder parserBuilder(pExecutor->getSolver(), filename, opts);

      if( inputFromStdin ) {
#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
        parserBuilder.withStreamInput(cin);
#else /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
        parserBuilder.withLineBufferedStreamInput(cin);
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
      }

      vector< vector<Command*> > allCommands;
      allCommands.push_back(vector<Command*>());
      std::unique_ptr<Parser> parser(parserBuilder.build());
      if(replayParser) {
        // have the replay parser use the file's declarations
        replayParser->useDeclarationsFrom(parser.get());
      }
      int needReset = 0;
      // true if one of the commands was interrupted
      bool interrupted = false;
      while (status)
      {
        if (interrupted) {
          (*opts.getOut()) << CommandInterrupted();
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
          if(needReset >= opts.getTearDownIncremental()) {
            pExecutor->reset();
            for(size_t i = 0; i < allCommands.size() && !interrupted; ++i) {
              if (interrupted) break;
              for(size_t j = 0; j < allCommands[i].size() && !interrupted; ++j)
              {
                Command* ccmd = allCommands[i][j]->clone();
                ccmd->setMuted(true);
                pExecutor->doCommand(ccmd);
                if (ccmd->interrupted())
                {
                  interrupted = true;
                }
                delete ccmd;
              }
            }
            needReset = 0;
          }
          allCommands.push_back(vector<Command*>());
          Command* copy = cmd->clone();
          allCommands.back().push_back(copy);
          status = pExecutor->doCommand(cmd);
          if(cmd->interrupted()) {
            interrupted = true;
            continue;
          }
        } else if(dynamic_cast<PopCommand*>(cmd) != NULL) {
          allCommands.pop_back(); // fixme leaks cmds here
          if (needReset >= opts.getTearDownIncremental()) {
            pExecutor->reset();
            for(size_t i = 0; i < allCommands.size() && !interrupted; ++i) {
              for(size_t j = 0; j < allCommands[i].size() && !interrupted; ++j)
              {
                Command* ccmd = allCommands[i][j]->clone();
                ccmd->setMuted(true);
                pExecutor->doCommand(ccmd);
                if (ccmd->interrupted())
                {
                  interrupted = true;
                }
                delete ccmd;
              }
            }
            if (interrupted) continue;
            (*opts.getOut()) << CommandSuccess();
            needReset = 0;
          } else {
            status = pExecutor->doCommand(cmd);
            if(cmd->interrupted()) {
              interrupted = true;
              continue;
            }
          }
        } else if(dynamic_cast<CheckSatCommand*>(cmd) != NULL ||
                  dynamic_cast<QueryCommand*>(cmd) != NULL) {
          if(needReset >= opts.getTearDownIncremental()) {
            pExecutor->reset();
            for(size_t i = 0; i < allCommands.size() && !interrupted; ++i) {
              for(size_t j = 0; j < allCommands[i].size() && !interrupted; ++j)
              {
                Command* ccmd = allCommands[i][j]->clone();
                ccmd->setMuted(true);
                pExecutor->doCommand(ccmd);
                if (ccmd->interrupted())
                {
                  interrupted = true;
                }
                delete ccmd;
              }
            }
            needReset = 0;
          } else {
            ++needReset;
          }
          if (interrupted) {
            continue;
          }

          status = pExecutor->doCommand(cmd);
          if(cmd->interrupted()) {
            interrupted = true;
            continue;
          }
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
    } else {
      if(!opts.wasSetByUserIncrementalSolving()) {
        cmd = new SetOptionCommand("incremental", SExpr(false));
        cmd->setMuted(true);
        pExecutor->doCommand(cmd);
        delete cmd;
      }

      ParserBuilder parserBuilder(pExecutor->getSolver(), filename, opts);

      if( inputFromStdin ) {
#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
        parserBuilder.withStreamInput(cin);
#else /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
        parserBuilder.withLineBufferedStreamInput(cin);
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */
      }

      std::unique_ptr<Parser> parser(parserBuilder.build());
      if(replayParser) {
        // have the replay parser use the file's declarations
        replayParser->useDeclarationsFrom(parser.get());
      }
      bool interrupted = false;
      while (status)
      {
        if (interrupted) {
          (*opts.getOut()) << CommandInterrupted();
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
    opts.flushOut();
    // exit, don't return (don't want destructors to run)
    // _exit() from unistd.h doesn't run global destructors
    // or other on_exit/atexit stuff.
    _exit(returnValue);
#endif /* CVC4_COMPETITION_MODE */

    ReferenceStat< Result > s_statSatResult("sat/unsat", result);
    RegisterStatistic statSatResultReg(&pExecutor->getStatisticsRegistry(),
                                       &s_statSatResult);

    pTotalTime->stop();

    // Tim: I think that following comment is out of date?
    // Set the global executor pointer to NULL first.  If we get a
    // signal while dumping statistics, we don't want to try again.
    pExecutor->flushOutputStreams();

#ifdef CVC4_DEBUG
    if(opts.getEarlyExit() && opts.wasSetByUserEarlyExit()) {
      _exit(returnValue);
    }
#else /* CVC4_DEBUG */
    if(opts.getEarlyExit()) {
      _exit(returnValue);
    }
#endif /* CVC4_DEBUG */
  }

  // On exceptional exit, these are leaked, but that's okay... they
  // need to be around in that case for main() to print statistics.
  delete pTotalTime;
  delete pExecutor;

  pTotalTime = NULL;
  pExecutor = NULL;

  cvc4_shutdown();

  return returnValue;
}
