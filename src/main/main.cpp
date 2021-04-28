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

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <unistd.h>

#include "base/configuration.h"
#include "base/output.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "options/language.h"
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
  Options opts;
  try {
    return runCvc5(argc, argv, opts);
  } catch(OptionException& e) {
#ifdef CVC5_COMPETITION_MODE
    *opts.getOut() << "unknown" << endl;
#endif
    cerr << "(error \"" << e << "\")" << endl
         << endl
         << "Please use --help to get help on command-line options." << endl;
  } catch(Exception& e) {
#ifdef CVC5_COMPETITION_MODE
    *opts.getOut() << "unknown" << endl;
#endif
    if (language::isOutputLang_smt2(opts.getOutputLanguage()))
    {
      *opts.getOut() << "(error \"" << e << "\")" << endl;
    } else {
      *opts.getErr() << "(error \"" << e << "\")" << endl;
    }
    if (opts.getStatistics() && pExecutor != nullptr)
    {
      totalTime.reset();
      pExecutor->printStatistics(*opts.getErr());
    }
  }
  exit(1);
}
