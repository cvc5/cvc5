/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Main driver for CVC4 executable
 **
 ** Main driver for CVC4 executable.
 **/
#include "main/main.h"

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <unistd.h>

#include "base/configuration.h"
#include "base/output.h"
#include "expr/expr_manager.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "smt/smt_engine.h"
#include "util/result.h"
#include "util/statistics.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::main;
using namespace CVC4::language;

/**
 * CVC4's main() routine is just an exception-safe wrapper around CVC4.
 * Please don't construct anything here.  Even if the constructor is
 * inside the try { }, an exception during destruction can cause
 * problems.  That's why main() wraps runCvc4() in the first place.
 * Put everything in runCvc4().
 */
int main(int argc, char* argv[]) {
  Options opts;
  try {
    return runCvc4(argc, argv, opts);
  } catch(OptionException& e) {
#ifdef CVC4_COMPETITION_MODE
    *opts.getOut() << "unknown" << endl;
#endif
    cerr << "(error \"" << e << "\")" << endl
         << endl
         << "Please use --help to get help on command-line options." << endl;
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *opts.getOut() << "unknown" << endl;
#endif
    if (language::isOutputLang_smt2(opts.getOutputLanguage()))
    {
      *opts.getOut() << "(error \"" << e << "\")" << endl;
    } else {
      *opts.getErr() << "(error \"" << e << "\")" << endl;
    }
    if(opts.getStatistics() && pExecutor != NULL) {
      pTotalTime->stop();
      pExecutor->flushStatistics(*opts.getErr());
    }
  }
  exit(1);
}
