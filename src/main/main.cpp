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
#include <cstring>
#include <new>

#include "config.h"
#include "main.h"
#include "usage.h"
#include "parser/parser.h"
#include "parser/smt/smt_parser.h"
#include "parser/cvc/cvc_parser.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "util/command.h"
#include "util/output.h"

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
    NodeManager exprMgr;

    // Create the SmtEngine
    SmtEngine smt(&exprMgr, &options);

    // If no file supplied we read from standard input
    bool inputFromStdin = firstArgIndex >= argc;

    if(!inputFromStdin && options.lang == Options::LANG_AUTO) {
      if(!strcmp(".smt", argv[firstArgIndex] + strlen(argv[firstArgIndex]) - 4))
        options.lang = Options::LANG_SMTLIB;
      else if(!strcmp(".cvc", argv[firstArgIndex] + strlen(argv[firstArgIndex]) - 4) ||
              !strcmp(".cvc4", argv[firstArgIndex] + strlen(argv[firstArgIndex]) - 5))
        options.lang = Options::LANG_CVC4;
    }

    if(options.smtcomp_mode) {
      Debug.setStream(CVC4::null_os);
      Trace.setStream(CVC4::null_os);
      Notice.setStream(CVC4::null_os);
      Chat.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    } else {
      if(options.verbosity < 2)
        Chat.setStream(CVC4::null_os);
      if(options.verbosity < 1)
        Notice.setStream(CVC4::null_os);
      if(options.verbosity < 0)
        Warning.setStream(CVC4::null_os);
    }

    const char* fname;
    istream* in;
    ifstream* file;
    if(inputFromStdin) {
      fname = "stdin";
      in = &cin;
    } else {
      fname = argv[firstArgIndex];
      file = new ifstream(fname);
      in = file;
    }

    // Create the parser
    Parser* parser;
    switch(options.lang) {
    case Options::LANG_SMTLIB:
      parser = new SmtParser(&exprMgr, *in, fname);
      break;
    case Options::LANG_CVC4:
      parser = new CvcParser(&exprMgr, *in, fname);
      break;
    case Options::LANG_AUTO:
      cerr << "Auto language detection not supported yet." << endl;
      abort();
    default:
      cerr << "Unknown language" << endl;
      abort();
    }

    // Parse and execute commands until we are done
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

    delete file;
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
