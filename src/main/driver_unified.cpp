/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Driver for cvc5 executable (cvc5).
 */

#include <cvc5/cvc5.h>
#include <stdio.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <new>
#include <optional>

#include "base/configuration.h"
#include "base/cvc5config.h"
#include "base/output.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "main/main.h"
#include "main/options.h"
#include "main/portfolio_driver.h"
#include "main/signal_handlers.h"
#include "main/time_limit.h"
#include "parser/api/cpp/command.h"
#include "parser/api/cpp/input_parser.h"
#include "smt/solver_engine.h"
#include "util/result.h"

using namespace std;
using namespace cvc5::internal;
using namespace cvc5::parser;
using namespace cvc5::main;

namespace cvc5::main {

/** Full argv[0] */
const char* progPath;

/** Just the basename component of argv[0] */
std::string progName;

/** A pointer to the CommandExecutor (the signal handlers need it) */
std::unique_ptr<CommandExecutor> pExecutor;

}  // namespace cvc5::main

int runCvc5(int argc, char* argv[], std::unique_ptr<cvc5::Solver>& solver)
{
  // Initialize the signal handlers
  signal_handlers::install();

  progPath = argv[0];

  // Create the command executor to execute the parsed commands
  pExecutor = std::make_unique<CommandExecutor>(solver);
  cvc5::DriverOptions dopts = solver->getDriverOptions();

  // Parse the options
  std::vector<string> filenames = parse(*solver, argc, argv, progName);
  if (solver->getOptionInfo("help").boolValue())
  {
    printUsage(progName, dopts.out());
    exit(1);
  }
  for (const auto& name : {"show-config",
                           "copyright",
                           "show-trace-tags",
                           "version"})
  {
    if (solver->getOptionInfo(name).boolValue())
    {
      std::exit(0);
    }
  }

  auto limit = install_time_limit(solver->getOptionInfo("tlimit").uintValue());
  segvSpin = solver->getOptionInfo("segv-spin").boolValue();

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC5_COMPETITION_MODE
  dopts.out() << unitbuf;
#endif /* CVC5_COMPETITION_MODE */

  // We only accept one input file
  if(filenames.size() > 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin = filenames.empty() || filenames[0] == "-";

  // If we're reading from stdin, use interactive mode if stdin-input-per-line
  // is true, or if we are a TTY.
  if (!solver->getOptionInfo("interactive").setByUser)
  {
    bool inputPerLine =
        solver->getOptionInfo("stdin-input-per-line").boolValue();
    solver->setOption(
        "interactive",
        (inputFromStdin && (inputPerLine || isatty(fileno(stdin)))) ? "true"
                                                                    : "false");
  }

  // Auto-detect input language by filename extension
  std::string filenameStr("<stdin>");
  if (!inputFromStdin) {
    filenameStr = std::move(filenames[0]);
  }
  const char* filename = filenameStr.c_str();

  if (solver->getOption("input-language") == "LANG_AUTO")
  {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      solver->setOption("input-language", "smt2");
    } else {
      size_t len = filenameStr.size();
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        solver->setOption("input-language", "smt2");
      } else if((len >= 3 && !strcmp(".sy", filename + len - 3))
                || (len >= 3 && !strcmp(".sl", filename + len - 3))) {
        // version 2 sygus is the default
        solver->setOption("input-language", "sygus2");
      }
    }
  }
  if (solver->getOption("input-language") == "LANG_SYGUS_V2")
  {
    // Enable the sygus API. We set this here instead of in set defaults 
    // to simplify checking at the API level. In particular, the sygus
    // option is the authority on whether sygus commands are currently
    // allowed in the API.
    solver->setOption("sygus", "true");
  }

  if (solver->getOption("output-language") == "LANG_AUTO")
  {
    solver->setOption("output-language", solver->getOption("input-language"));
  }
  pExecutor->storeOptionsAsOriginal();

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    TraceChannel.setStream(&cvc5::internal::null_os);
    WarningChannel.setStream(&cvc5::internal::null_os);
  }

  int returnValue = 0;
  {
    solver->setInfo("filename", filenameStr);

    // Parse and execute commands until we are done
    if (solver->getOptionInfo("interactive").boolValue() && inputFromStdin)
    {
      // We use the interactive shell when piping from stdin, even some cases
      // where the input stream is not a TTY. We do this to avoid memory issues
      // involving tokens that span multiple lines.
      // We compute whether the interactive shell is actually interactive
      // (via isatty). If we are not interactive, we disable certain output
      // information, e.g. for querying the user.
      bool isInteractive = isatty(fileno(stdin));
      // set incremental if we are in interactive mode
      if (!solver->getOptionInfo("incremental").setByUser)
      {
        solver->setOption("incremental", isInteractive ? "true" : "false");
      }
      InteractiveShell shell(
          pExecutor.get(), dopts.in(), dopts.out(), isInteractive);

      if (isInteractive)
      {
        auto& out = solver->getDriverOptions().out();
        out << Configuration::getPackageName() << " "
            << Configuration::getVersionString();
        if (Configuration::isGitBuild())
        {
          out << " [" << Configuration::getGitInfo() << "]";
        }
        out << (Configuration::isDebugBuild() ? " DEBUG" : "") << " assertions:"
            << (Configuration::isAssertionBuild() ? "on" : "off") << std::endl
            << std::endl
            << Configuration::copyright() << std::endl;
      }

      while (true)
      {
        // read and execute all available commands
        if (!shell.readAndExecCommands())
        {
          break;
        }
      }
    }
    else
    {
      if (!solver->getOptionInfo("incremental").setByUser)
      {
        solver->setOption("incremental", "false");
      }
      // we don't need to check that terms passed to API methods are well
      // formed, since this should be an invariant of the parser
      if (!solver->getOptionInfo("wf-checking").setByUser)
      {
        solver->setOption("wf-checking", "false");
      }

      std::unique_ptr<InputParser> parser(new InputParser(
          pExecutor->getSolver(), pExecutor->getSymbolManager()));
      if( inputFromStdin ) {
        parser->setStreamInput(
            solver->getOption("input-language"), cin, filename);
      }
      else
      {
        parser->setFileInput(solver->getOption("input-language"), filename);
      }

      PortfolioDriver driver(parser);
      returnValue = driver.solve(pExecutor) ? 0 : 1;
    }

#ifdef CVC5_COMPETITION_MODE
    dopts.out() << std::flush;
    // exit, don't return (don't want destructors to run)
    // _exit() from unistd.h doesn't run global destructors
    // or other on_exit/atexit stuff.
    _exit(returnValue);
#endif /* CVC5_COMPETITION_MODE */

    pExecutor->flushOutputStreams();

#ifdef CVC5_DEBUG
    {
      auto info = solver->getOptionInfo("early-exit");
      if (info.boolValue() && info.setByUser)
      {
        _exit(returnValue);
      }
    }
#else  /* CVC5_DEBUG */
    if (solver->getOptionInfo("early-exit").boolValue())
    {
      _exit(returnValue);
    }
#endif /* CVC5_DEBUG */
  }

  pExecutor.reset();

  signal_handlers::cleanup();

  return returnValue;
}
