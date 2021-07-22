/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Liana Hadarean, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Driver for cvc5 executable (cvc5).
 */

#include <stdio.h>
#include <unistd.h>

#include <chrono>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <new>

#include "api/cpp/cvc5.h"
#include "base/configuration.h"
#include "base/cvc5config.h"
#include "base/output.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "main/main.h"
#include "main/signal_handlers.h"
#include "main/time_limit.h"
#include "options/base_options.h"
#include "options/options.h"
#include "options/parser_options.h"
#include "options/main_options.h"
#include "options/set_language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"
#include "smt/smt_engine.h"
#include "util/result.h"

using namespace std;
using namespace cvc5;
using namespace cvc5::parser;
using namespace cvc5::main;

namespace cvc5 {
namespace main {

/** Full argv[0] */
const char* progPath;

/** Just the basename component of argv[0] */
std::string progName;

/** A pointer to the CommandExecutor (the signal handlers need it) */
std::unique_ptr<cvc5::main::CommandExecutor> pExecutor;

/** The time point the binary started, accessible to signal handlers */
std::unique_ptr<TotalTimer> totalTime;

TotalTimer::~TotalTimer()
{
  if (pExecutor != nullptr)
  {
    auto duration = std::chrono::steady_clock::now() - d_start;
    pExecutor->getSmtEngine()->setTotalTimeStatistic(
        std::chrono::duration<double>(duration).count());
  }
    }

    }  // namespace main
    }  // namespace cvc5

void printUsage(const Options& opts, bool full) {
  stringstream ss;
  ss << "usage: " << progName << " [options] [input-file]"
     << endl
     << endl
     << "Without an input file, or with `-', cvc5 reads from standard input."
     << endl
     << endl
     << "cvc5 options:" << endl;
  if(full) {
    Options::printUsage(ss.str(), *opts.base.out);
  } else {
    Options::printShortUsage(ss.str(), *opts.base.out);
  }
}

int runCvc5(int argc, char* argv[], Options& opts)
{
  main::totalTime = std::make_unique<TotalTimer>();

  // Initialize the signal handlers
  signal_handlers::install();

  progPath = argv[0];

  // Parse the options
  std::vector<string> filenames =
      Options::parseOptions(&opts, argc, argv, progName);

  auto limit = install_time_limit(opts);

  if (opts.driver.help)
  {
    printUsage(opts, true);
    exit(1);
  }
  else if (opts.base.languageHelp)
  {
    Options::printLanguageHelp(*opts.base.out);
    exit(1);
  }
  else if (opts.driver.version)
  {
    *opts.base.out << Configuration::about().c_str() << flush;
    exit(0);
  }

  segvSpin = opts.driver.segvSpin;

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC5_COMPETITION_MODE
  *opts.base.out << unitbuf;
#endif /* CVC5_COMPETITION_MODE */

  // We only accept one input file
  if(filenames.size() > 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin = filenames.empty() || filenames[0] == "-";

  // if we're reading from stdin on a TTY, default to interactive mode
  if (!opts.driver.interactiveWasSetByUser)
  {
    opts.driver.interactive = inputFromStdin && isatty(fileno(stdin));
  }

  // Auto-detect input language by filename extension
  std::string filenameStr("<stdin>");
  if (!inputFromStdin) {
    // Use swap to avoid copying the string
    // TODO: use std::move() when switching to c++11
    filenameStr.swap(filenames[0]);
  }
  const char* filename = filenameStr.c_str();

  if (opts.base.inputLanguage == language::input::LANG_AUTO)
  {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      opts.base.inputLanguage = language::input::LANG_CVC;
    } else {
      size_t len = filenameStr.size();
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        opts.base.inputLanguage = language::input::LANG_SMTLIB_V2_6;
      } else if((len >= 2 && !strcmp(".p", filename + len - 2))
                || (len >= 5 && !strcmp(".tptp", filename + len - 5))) {
        opts.base.inputLanguage = language::input::LANG_TPTP;
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        opts.base.inputLanguage = language::input::LANG_CVC;
      } else if((len >= 3 && !strcmp(".sy", filename + len - 3))
                || (len >= 3 && !strcmp(".sl", filename + len - 3))) {
        // version 2 sygus is the default
        opts.base.inputLanguage = language::input::LANG_SYGUS_V2;
      }
    }
  }

  if (opts.base.outputLanguage == language::output::LANG_AUTO)
  {
    opts.base.outputLanguage = language::toOutputLanguage(opts.base.inputLanguage);
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(&cvc5::null_os);
    TraceChannel.setStream(&cvc5::null_os);
    NoticeChannel.setStream(&cvc5::null_os);
    ChatChannel.setStream(&cvc5::null_os);
    MessageChannel.setStream(&cvc5::null_os);
    WarningChannel.setStream(&cvc5::null_os);
  }

  // important even for muzzled builds (to get result output right)
  (*opts.base.out)
      << language::SetLanguage(opts.base.outputLanguage);

  // Create the command executor to execute the parsed commands
  pExecutor = std::make_unique<CommandExecutor>(opts);

  int returnValue = 0;
  {
    // notify SmtEngine that we are starting to parse
    pExecutor->getSmtEngine()->notifyStartParsing(filenameStr);

    // Parse and execute commands until we are done
    std::unique_ptr<Command> cmd;
    bool status = true;
    if (opts.driver.interactive && inputFromStdin)
    {
      if (!opts.base.incrementalSolvingWasSetByUser)
      {
        cmd.reset(new SetOptionCommand("incremental", "true"));
        cmd->setMuted(true);
        pExecutor->doCommand(cmd);
      }
      InteractiveShell shell(pExecutor->getSolver(),
                             pExecutor->getSymbolManager());
      if (opts.driver.interactivePrompt)
      {
        CVC5Message() << Configuration::getPackageName() << " "
                      << Configuration::getVersionString();
        if(Configuration::isGitBuild()) {
          CVC5Message() << " [" << Configuration::getGitId() << "]";
        }
        CVC5Message() << (Configuration::isDebugBuild() ? " DEBUG" : "")
                      << " assertions:"
                      << (Configuration::isAssertionBuild() ? "on" : "off")
                      << endl
                      << endl;
        CVC5Message() << Configuration::copyright() << endl;
      }

      while(true) {
        try {
          cmd.reset(shell.readCommand());
        } catch(UnsafeInterruptException& e) {
          *opts.base.out << CommandInterrupted();
          break;
        }
        if (cmd == nullptr)
          break;
        status = pExecutor->doCommand(cmd) && status;
        if (cmd->interrupted()) {
          break;
        }
      }
    }
    else
    {
      if (!opts.base.incrementalSolvingWasSetByUser)
      {
        cmd.reset(new SetOptionCommand("incremental", "false"));
        cmd->setMuted(true);
        pExecutor->doCommand(cmd);
      }

      ParserBuilder parserBuilder(pExecutor->getSolver(),
                                  pExecutor->getSymbolManager(),
                                  opts);
      std::unique_ptr<Parser> parser(parserBuilder.build());
      if( inputFromStdin ) {
        parser->setInput(Input::newStreamInput(
            opts.base.inputLanguage, cin, filename));
      }
      else
      {
        parser->setInput(Input::newFileInput(opts.base.inputLanguage,
                                             filename,
                                             opts.parser.memoryMap));
      }

      bool interrupted = false;
      while (status)
      {
        if (interrupted) {
          *opts.base.out << CommandInterrupted();
          pExecutor->reset();
          break;
        }
        try {
          cmd.reset(parser->nextCommand());
          if (cmd == nullptr) break;
        } catch (UnsafeInterruptException& e) {
          interrupted = true;
          continue;
        }

        status = pExecutor->doCommand(cmd);
        if (cmd->interrupted() && status == 0) {
          interrupted = true;
          break;
        }

        if(dynamic_cast<QuitCommand*>(cmd.get()) != nullptr) {
          break;
        }
      }
    }

    api::Result result;
    if(status) {
      result = pExecutor->getResult();
      returnValue = 0;
    } else {
      // there was some kind of error
      returnValue = 1;
    }

#ifdef CVC5_COMPETITION_MODE
    if (opts.base.out != nullptr)
    {
      *opts.base.out << std::flush;
    }
    // exit, don't return (don't want destructors to run)
    // _exit() from unistd.h doesn't run global destructors
    // or other on_exit/atexit stuff.
    _exit(returnValue);
#endif /* CVC5_COMPETITION_MODE */

    totalTime.reset();
    pExecutor->flushOutputStreams();

#ifdef CVC5_DEBUG
    if (opts.driver.earlyExit && opts.driver.earlyExitWasSetByUser)
    {
      _exit(returnValue);
    }
#else  /* CVC5_DEBUG */
    if (opts.driver.earlyExit)
    {
      _exit(returnValue);
    }
#endif /* CVC5_DEBUG */
  }

  pExecutor.reset();

  signal_handlers::cleanup();

  return returnValue;
}
