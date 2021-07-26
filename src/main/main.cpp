/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Main driver for cvc5 executable.
 */
#include "main/main.h"

#include <stdio.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>

#include "api/cpp/cvc5.h"
#include "base/configuration.h"
#include "base/output.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/base_options.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "util/result.h"

using namespace std;
using namespace cvc5;
using namespace cvc5::main;
using namespace cvc5::language;

/**
 * cvc5's main() routine is just an exception-safe wrapper around cvc5.
 * Please don't construct anything here.  Even if the constructor is
 * inside the try { }, an exception during destruction can cause
 * problems.  That's why main() wraps runCvc5() in the first place.
 * Put everything in runCvc5().
 */
int main(int argc, char* argv[]) {
  std::unique_ptr<api::Solver> solver;
  try {
    solver = std::make_unique<api::Solver>();
    return runCvc5(argc, argv, solver);
  } catch(OptionException& e) {
#ifdef CVC5_COMPETITION_MODE
    *solver->getOptions().base.out << "unknown" << endl;
#endif
    cerr << "(error \"" << e << "\")" << endl
         << endl
         << "Please use --help to get help on command-line options." << endl;
  } catch(Exception& e) {
#ifdef CVC5_COMPETITION_MODE
    *solver->getOptions().base.out << "unknown" << endl;
#endif
    if (language::isOutputLang_smt2(solver->getOptions().base.outputLanguage))
    {
      *solver->getOptions().base.out << "(error \"" << e << "\")" << endl;
    } else {
      *solver->getOptions().base.err << "(error \"" << e << "\")" << endl;
    }
    if (solver->getOptions().base.statistics && pExecutor != nullptr)
    {
      totalTime.reset();
      pExecutor->printStatistics(*solver->getOptions().base.err);
    }
  }
  exit(1);
}
