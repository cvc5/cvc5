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
#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <new>
#include <exception>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include "config.h"
#include "main.h"
#include "usage.h"
#include "parser/parser.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "parser/language.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

int main(int argc, char *argv[]) {
  struct Options opts;

  try {
    cvc4_init();

    int firstArgIndex = parseOptions(argc, argv, &opts);

    istream *in;
    ifstream infile;
    Language lang = PL;

    if(firstArgIndex >= argc) {
      in = &cin;
    } else if(argc > firstArgIndex + 1) {
      throw new Exception("Too many input files specified.");
    } else {
      in = &infile;
      if(strlen(argv[firstArgIndex]) >= 4 && !strcmp(argv[firstArgIndex] + strlen(argv[firstArgIndex]) - 4, ".smt"))
        lang = SMTLIB;
      infile.open(argv[firstArgIndex], ifstream::in);

      if(!infile) {
        throw new Exception(string("Could not open input file `") + argv[firstArgIndex] + "' for reading: " + strerror(errno));
        exit(1);
      }
    }

    ExprManager *exprMgr = new ExprManager();
    SmtEngine smt(exprMgr, &opts);
    Parser parser(&smt, lang, *in, &opts);
    while(!parser.done()) {
      Command *cmd = parser.next();
      cmd->invoke();
      delete cmd;
    }
  } catch(CVC4::main::OptionException* e) {
    if(opts.smtcomp_mode) {
      printf("unknown");
      fflush(stdout);
    }
    fprintf(stderr, "CVC4 Error:\n%s\n\n", e->toString().c_str());
    printf(usage, opts.binary_name.c_str());
    exit(1);
  } catch(CVC4::Exception* e) {
    if(opts.smtcomp_mode) {
      printf("unknown");
      fflush(stdout);
    }
    fprintf(stderr, "CVC4 Error:\n%s\n", e->toString().c_str());
    exit(1);
  } catch(bad_alloc) {
    if(opts.smtcomp_mode) {
      printf("unknown");
      fflush(stdout);
    }
    fprintf(stderr, "CVC4 ran out of memory.\n");
    exit(1);
  } catch(...) {
    fprintf(stderr, "CVC4 threw an exception of unknown type.\n");
    exit(1);
  }

  return 0;
}
