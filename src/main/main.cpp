/*********************                                                        */
/** main.cpp
 ** Original author: mdeters
 ** Major contributors: barrett, dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Main driver for CVC4 executable.
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
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/result.h"
#include "util/Assert.h"
#include "util/output.h"
#include "util/options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

static Result lastResult;
static struct Options options;

void doCommand(SmtEngine&, Command*);

int main(int argc, char *argv[]) {

  try {

    // Initialize the signal handlers
    cvc4_init();

    // Parse the options
    int firstArgIndex = parseOptions(argc, argv, &options);

    // If in competition mode, set output stream option to flush immediately
    if(options.smtcomp_mode) {
      cout << unitbuf;
    }

    // We only accept one input file
    if(argc > firstArgIndex + 1) {
      throw Exception("Too many input files specified.");
    }

    // Create the expression manager
    ExprManager exprMgr;

    // Create the SmtEngine
    SmtEngine smt(&exprMgr, &options);

    // If no file supplied we read from standard input
    bool inputFromStdin = firstArgIndex >= argc;

    // Auto-detect input language by filename extension
    if(!inputFromStdin && options.lang == Parser::LANG_AUTO) {
      if(!strcmp(".smt", argv[firstArgIndex] + strlen(argv[firstArgIndex]) - 4)) {
        options.lang = Parser::LANG_SMTLIB;
      } else if(!strcmp(".cvc", argv[firstArgIndex]
          + strlen(argv[firstArgIndex]) - 4)
          || !strcmp(".cvc4", argv[firstArgIndex] + strlen(argv[firstArgIndex])
              - 5)) {
        options.lang = Parser::LANG_CVC4;
      }
    }

    // Determine which messages to show based on smtcomp_mode and verbosity
    if(options.smtcomp_mode) {
      Debug.setStream(CVC4::null_os);
      Trace.setStream(CVC4::null_os);
      Notice.setStream(CVC4::null_os);
      Chat.setStream(CVC4::null_os);
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    } else {
      if(options.verbosity < 2) {
        Chat.setStream(CVC4::null_os);
      }
      if(options.verbosity < 1) {
        Notice.setStream(CVC4::null_os);
      }
      if(options.verbosity < 0) {
        Message.setStream(CVC4::null_os);
        Warning.setStream(CVC4::null_os);
      }
    }

    // Create the parser
    Parser* parser;
    if(inputFromStdin) {
      parser = Parser::getNewParser(&exprMgr, options.lang, cin);
    } else {
      parser = Parser::getNewParser(&exprMgr, options.lang, argv[firstArgIndex]);
    }

    // Parse and execute commands until we are done
    Command* cmd;
    while((cmd = parser->parseNextCommand())) {
      doCommand(smt, cmd);
      delete cmd;
    }

    // Remove the parser
    delete parser;

  } catch(OptionException& e) {
    if(options.smtcomp_mode) {
      cout << "unknown" << endl;
    }
    cerr << "CVC4 Error:" << endl << e << endl;
    printf(usage, options.binary_name.c_str());
    abort();
  } catch(Exception& e) {
    if(options.smtcomp_mode) {
      cout << "unknown" << endl;
    }
    cerr << "CVC4 Error:" << endl << e << endl;
    abort();
  } catch(bad_alloc) {
    if(options.smtcomp_mode) {
      cout << "unknown" << endl;
    }
    cerr << "CVC4 ran out of memory." << endl;
    abort();
  } catch(...) {
    if(options.smtcomp_mode) {
      cout << "unknown" << endl;
    }
    cerr << "CVC4 threw an exception of unknown type." << endl;
    abort();
  }

  switch(lastResult.asSatisfiabilityResult().isSAT()) {

  case Result::SAT:
    return 10;

  case Result::UNSAT:
    return 20;

  default:
    return 0;

  }
}

void doCommand(SmtEngine& smt, Command* cmd) {
  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      doCommand(smt, *subcmd);
    }
  } else {
    if(options.verbosity > 0) {
      cout << "Invoking: " << *cmd << endl;
    }

    cmd->invoke(&smt);

    QueryCommand *qc = dynamic_cast<QueryCommand*>(cmd);
    if(qc != NULL) {
      lastResult = qc->getResult();
      if(options.verbosity >= 0) {
        cout << lastResult << endl;
      }
    } else {
      CheckSatCommand *csc = dynamic_cast<CheckSatCommand*>(cmd);
      if(csc != NULL) {
        lastResult = csc->getResult();
        if(options.verbosity >= 0) {
          cout << lastResult << endl;
        }
      }
    }
  }
}
