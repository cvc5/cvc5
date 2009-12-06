/*********************                                           -*- C++ -*-  */
/** main.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <new>

#include "config.h"
#include "main.h"
#include "usage.h"
#include "parser/parser.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "util/command.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

int main(int argc, char *argv[]) {

  struct Options options;

  try {

    // Initialize the signal handlers
    cvc4_init();

    // Parse the options
    int firstArgIndex = parseOptions(argc, argv, &options);

    // If in competition mode, we flush the stdout immediately
    if(options.smtcomp_mode)
      cout << unitbuf;

        // We only accept one input file
    if(argc > firstArgIndex + 1)
      throw new Exception("Too many input files specified.");

    // Create the expression manager
    ExprManager exprMgr;
    // Create the SmtEngine
    SmtEngine smt(&exprMgr, &options);

    // If no file supplied we read from standard input
    bool inputFromStdin = firstArgIndex >= argc;

    // Create the parser
    Parser* parser;
    switch(options.lang) {
    case Options::LANG_SMTLIB:
      if(inputFromStdin)
        parser = new SmtParser(&exprMgr, cin);
      else
        parser = new SmtParser(&exprMgr, argv[firstArgIndex]);
      break;
    default:
      cerr << "Language" << options.lang << "not supported yet." << endl;
      abort();
    }

    // Parse the and execute commands until we are done
    while(!parser->done()) {
      // Parse the next command
      Command *cmd = parser->parseNextCommand();
      if(cmd) {
        if(options.verbosity > 0)
          cout << "Invoking: " << *cmd << endl;
        cmd->invoke(&smt);
        delete cmd;
      }
    }

    // Remove the parser
    delete parser;
  } catch(OptionException& e) {
    if(options.smtcomp_mode)
      cout << "unknown" << endl;
    cerr << "CVC4 Error:" << endl << e << endl;
    printf(usage, options.binary_name.c_str());
    abort();
  } catch(CVC4::Exception& e) {
    if(options.smtcomp_mode)
      cout << "unknown" << endl;
    cerr << "CVC4 Error:" << endl << e << endl;
    abort();
  } catch(bad_alloc) {
    if(options.smtcomp_mode)
      cout << "unknown" << endl;
    cerr << "CVC4 ran out of memory." << endl;
    abort();
  } catch(...) {
    cerr << "CVC4 threw an exception of unknown type." << endl;
    abort();
  }

  return 0;
}
