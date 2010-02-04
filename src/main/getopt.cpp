/*********************                                           -*- C++ -*-  */
/** getopt.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): barrett, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Contains code for handling command-line options
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
#include "util/options.h"
#include "parser/parser.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;

namespace CVC4 {
namespace main {

static const char lang_help[] = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto          attempt to automatically determine the input language\n\
  pl | cvc4     CVC4 presentation language\n\
  smt | smtlib  SMT-LIB format\n\
";

static const char cnf_help[] = "\
CNF conversions currently supported as arguments to the --cnf option:\n\
  direct  put in equiv. CNF directly (exp. blow up in # clauses, no new vars)\n\
  var     variable-introduction method (new vars, no exp. blow up in # clauses)\n\
";

// FIXME add a comment here describing the purpose of this
enum OptionValue {
  CNF = 256, /* no clash with char options */
  SMTCOMP,
  STATS,
  SEGV_NOSPIN
};/* enum OptionValue */

// FIXME add a comment here describing the option array
static struct option cmdlineOptions[] = {
  // name, has_arg, *flag, val
  { "help"       , no_argument      , NULL, 'h'         },
  { "version"    , no_argument      , NULL, 'V'         },
  { "verbose"    , no_argument      , NULL, 'v'         },
  { "quiet"      , no_argument      , NULL, 'q'         },
  { "lang"       , required_argument, NULL, 'L'         },
  { "debug"      , required_argument, NULL, 'd'         },
  { "cnf"        , required_argument, NULL, CNF         },
  { "smtcomp"    , no_argument      , NULL, SMTCOMP     },
  { "stats"      , no_argument      , NULL, STATS       },
  { "segv-nospin", no_argument      , NULL, SEGV_NOSPIN }
};/* if you add things to the above, please remember to update usage.h! */

/** Full argv[0] */
const char *progPath;

/** Just the basename component of argv[0] */
const char *progName;

/** Parse argc/argv and put the result into a CVC4::Options struct. */
int parseOptions(int argc, char** argv, CVC4::Options* opts)
throw(OptionException) {
  progPath = progName = argv[0];
  int c;

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL) {
    progName = x + 1;
  }
  opts->binary_name = string(progName);

  // FIXME add a comment here describing the option string
  while((c = getopt_long(argc, argv,
                         "+:hVvqL:d:",
                         cmdlineOptions, NULL)) != -1) {
    switch(c) {

    case 'h':
      printf(usage, opts->binary_name.c_str());
      exit(1);

    case 'V':
      fputs(about, stdout);
      exit(0);

    case 'v':
      ++opts->verbosity;
      break;

    case 'q':
      --opts->verbosity;
      break;

    case 'L':
      if(!strcmp(optarg, "cvc4") || !strcmp(optarg, "pl")) {
        opts->lang = Parser::LANG_CVC4;
        break;
      } else if(!strcmp(optarg, "smtlib") || !strcmp(optarg, "smt")) {
        opts->lang = Parser::LANG_SMTLIB;
        break;
      } else if(!strcmp(optarg, "auto")) {
        opts->lang = Parser::LANG_AUTO;
        break;
      }

      if(strcmp(optarg, "help")) {
        throw OptionException(string("unknown language for --lang: `") +
                              optarg + "'.  Try --lang help.");
      }

      fputs(lang_help, stdout);
      exit(1);

    case CNF:
      if(!strcmp(optarg, "direct")) {
        opts->d_cnfConversion = CNF_DIRECT_EXPONENTIAL;
        break;
      } else if(!strcmp(optarg, "var")) {
        opts->d_cnfConversion = CNF_VAR_INTRODUCTION;
        break;
      } else if(strcmp(optarg, "help")) {
        throw OptionException(string("unknown CNF conversion for --cnf: `") +
                              optarg + "'.  Try --cnf help.");
      }

      fputs(cnf_help, stdout);
      exit(1);

    case 'd':
      Debug.on(optarg);
      /* fall-through */

    case STATS:
      opts->statistics = true;
      break;

    case SEGV_NOSPIN:
      segvNoSpin = true;
      break;

    case SMTCOMP:
      // silences CVC4 (except "sat" or "unsat" or "unknown", forces smtlib input)
      opts->smtcomp_mode = true;
      opts->verbosity = -1;
      opts->lang = Parser::LANG_SMTLIB;
      break;

    case '?':
      throw OptionException(string("can't understand option"));// + argv[optind - 1] + "'");

    case ':':
      throw OptionException(string("option missing its required argument"));// + argv[optind - 1] + "' missing its required argument");

    default:
      throw OptionException(string("can't understand option"));//: `") + argv[optind - 1] + "'");
    }

  }

  return optind;
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
