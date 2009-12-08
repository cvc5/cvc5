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
#include "util/output.h"

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

int parseOptions(int argc, char** argv, CVC4::Options* opts) throw(OptionException) {
  const char *progName = argv[0];
  int c;

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL)
    progName = x + 1;
  opts->binary_name = string(progName);

  while((c = getopt_long(argc, argv, "+:hVvqL:d:", cmdlineOptions, NULL)) != -1) {
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
      if(!strcmp(optarg, "cvc4") || !strcmp(optarg, "pl")) {
        opts->lang = Options::LANG_CVC4;
        break;
      } else if(!strcmp(optarg, "smtlib") || !strcmp(optarg, "smt")) {
        opts->lang = Options::LANG_SMTLIB;
        break;
      } else if(!strcmp(optarg, "auto")) {
        opts->lang = Options::LANG_AUTO;
        break;
      }

      if(strcmp(optarg, "help"))
        throw OptionException(string("unknown language for --lang: `") + argv[optind] + "'.  Try --lang help.");

      fputs(lang_help, stdout);
      exit(1);

    case 'd':
      Debug.on(optarg);

    case STATS:
      opts->statistics = true;
      break;

    case SMTCOMP:
      // silences CVC4 (except "sat" or "unsat" or "unknown", forces smtlib input)
      opts->smtcomp_mode = true;
      opts->verbosity = -1;
      opts->lang = Options::LANG_SMTLIB;
      break;

    case '?':
      throw OptionException(string("can't understand option: `") + argv[optind] + "'");

    case ':':
      throw OptionException(string("option `") + argv[optind] + "' missing its required argument");

    default:
      throw OptionException(string("can't understand option: `") + argv[optind] + "'");
    }

  }

  return optind;
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
