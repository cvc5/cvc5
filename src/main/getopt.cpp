/*********************                                           -*- C++ -*-  */
/** getopt.cpp
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
#include <new>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include <getopt.h>

#include "config.h"
#include "main.h"
#include "util/exception.h"
#include "usage.h"
#include "about.h"

using namespace std;
using namespace CVC4;

namespace CVC4 {
namespace main {

static const char lang_help[] = "\
Languages currently supported to the -L / --lang option:\n\
  auto          attempt to automatically determine the input language\n\
  pl | cvc4     CVC4 presentation language\n\
  smt | smtlib  SMT-LIB format\n\
";

enum Language {
  AUTO = 0,
  PL,
  SMTLIB,
};/* enum Language */

enum OptionValue {
  SMTCOMP = 256, /* no clash with char options */
  STATS
};/* enum OptionValue */

static struct option cmdlineOptions[] = {
  // name, has_arg, *flag, val
  { "help"   , no_argument      , NULL, 'h'     },
  { "version", no_argument      , NULL, 'V'     },
  { "verbose", no_argument      , NULL, 'v'     },
  { "quiet"  , no_argument      , NULL, 'q'     },
  { "lang"   , required_argument, NULL, 'L'     },
  { "debug"  , required_argument, NULL, 'd'     },
  { "smtcomp", no_argument      , NULL, SMTCOMP },
  { "stats"  , no_argument      , NULL, STATS   }
};

int parseOptions(int argc, char** argv, CVC4::Options* opts) throw(Exception*) {
  const char *progName = argv[0];
  int c;

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL)
    progName = x + 1;
  opts->binary_name = string(progName);

  while((c = getopt_long(argc, argv, "+:hVvL:", cmdlineOptions, NULL)) != -1) {
    switch(c) {

    case 'h':
      printf(usage, opts->binary_name.c_str());
      exit(1);
      break;

    case 'V':
      fputs(about, stdout);
      break;

    case 'v':
      ++opts->verbosity;
      break;

    case 'q':
      --opts->verbosity;
      break;

    case 'L':
      if(!strcmp(argv[optind], "cvc4") || !strcmp(argv[optind], "pl")) {
        opts->lang = PL;
        break;
      } else if(!strcmp(argv[optind], "smtlib") || !strcmp(argv[optind], "smt")) {
        opts->lang = SMTLIB;
        break;
      } else if(!strcmp(argv[optind], "auto")) {
        opts->lang = AUTO;
        break;
      }

      if(strcmp(argv[optind], "help"))
        throw new OptionException(string("unknown language for --lang: `") + argv[optind] + "'.  Try --lang help.");

      fputs(lang_help, stdout);
      exit(1);

    case STATS:
      opts->statistics = true;
      break;

    case SMTCOMP:
      // silences CVC4 (except "sat" or "unsat" or "unknown", forces smtlib input)
      opts->smtcomp_mode = true;
      opts->verbosity = -1;
      opts->lang = SMTLIB;
      break;

    case '?':
      throw new OptionException(string("can't understand option: `") + argv[optind] + "'");

    case ':':
      throw new OptionException(string("option `") + argv[optind] + "' missing its required argument");

    default:
      throw new OptionException(string("can't understand option: `") + argv[optind] + "'");
    }

  }

  return optind;
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
