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

using namespace std;
using namespace CVC4;
using namespace CVC4::main;

int main(int argc, char *argv[]) {
  struct Options opts;

  try {
    cvc4_init();

    int firstArgIndex = parseOptions(argc, argv, &opts);

    FILE *infile;

    if(firstArgIndex >= argc) {
      infile = stdin;
    } else if(argc > firstArgIndex + 1) {
      throw new Exception("Too many input files specified.");
    } else {
      infile = fopen(argv[firstArgIndex], "r");
      if(!infile) {
        throw new Exception(string("Could not open input file `") + argv[firstArgIndex] + "' for reading: " + strerror(errno));
        exit(1);
      }

      // ExprManager *exprMgr = ...;
      // SmtEngine smt(exprMgr, &opts);
      // Parser parser(infile, exprMgr, &opts);
      // while(!parser.done) {
      //   Command *cmd = parser.get();
      //   cmd->invoke(smt);
      //   delete cmd;
      // }
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
