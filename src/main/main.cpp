/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Main driver for cvc5 executable.
 */
#include "main/main.h"

#include <cvc5/cvc5.h>

#include <iostream>

#include "base/configuration.h"
#include "main/command_executor.h"
#include "options/option_exception.h"

using namespace cvc5::internal;
using namespace cvc5::main;

/**
 * cvc5's main() routine is just an exception-safe wrapper around runCvc5.
 */
int main(int argc, char* argv[])
{
  std::unique_ptr<cvc5::Solver> solver = std::make_unique<cvc5::Solver>();
  try
  {
    return runCvc5(argc, argv, solver);
  }
  catch (cvc5::CVC5ApiOptionException& e)
  {
#ifdef CVC5_COMPETITION_MODE
    solver->getDriverOptions().out() << "unknown" << std::endl;
#endif
    std::cerr << "(error \"" << e.getMessage() << "\")" << std::endl
              << std::endl
              << "Please use --help to get help on command-line options."
              << std::endl;
  }
  catch (OptionException& e)
  {
#ifdef CVC5_COMPETITION_MODE
    solver->getDriverOptions().out() << "unknown" << std::endl;
#endif
    std::cerr << "(error \"" << e.getMessage() << "\")" << std::endl
              << std::endl
              << "Please use --help to get help on command-line options."
              << std::endl;
  }
  catch (Exception& e)
  {
#ifdef CVC5_COMPETITION_MODE
    solver->getDriverOptions().out() << "unknown" << std::endl;
#endif
    if (solver->getOption("output-language") == "LANG_SMTLIB_V2_6")
    {
      solver->getDriverOptions().out()
          << "(error \"" << e << "\")" << std::endl;
    }
    else
    {
      solver->getDriverOptions().err()
          << "(error \"" << e << "\")" << std::endl;
    }
    if (solver->getOptionInfo("stats").boolValue() && pExecutor != nullptr)
    {
      pExecutor->printStatistics(solver->getDriverOptions().err());
    }
  }
  // Make sure that the command executor is destroyed before the node manager.
  pExecutor.reset();
  exit(1);
}
