/*********************                                                        */
/*! \file getopt.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): dejan, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Contains code for handling command-line options.
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

#include "util/exception.h"
#include "util/configuration.h"
#include "util/output.h"
#include "util/options.h"
#include "parser/parser_options.h"
#include "expr/expr.h"

#include "cvc4autoconfig.h"
#include "main.h"
#include "usage.h"

using namespace std;
using namespace CVC4;

namespace CVC4 {
namespace main {

static const char lang_help[] = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto           attempt to automatically determine the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
";

/**
 * For the main getopt() routine, we need ways to switch on long
 * options without clashing with short option characters.  This is an
 * enum of those long options.  For long options (e.g. "--verbose")
 * with a short option equivalent ("-v"), we use the single-letter
 * short option; therefore, this enumeration starts at 256 to avoid
 * any collision.
 */
enum OptionValue {
  SMTCOMP = 256, /* no clash with char options */
  STATS,
  SEGV_NOSPIN,
  PARSE_ONLY,
  NO_CHECKING,
  USE_MMAP,
  SHOW_CONFIG,
  STRICT_PARSING,
  DEFAULT_EXPR_DEPTH,
  PRINT_EXPR_TYPES,
  UF_THEORY
};/* enum OptionValue */

/**
 * This is a table of long options.  By policy, each short option
 * should have an equivalent long option (but the reverse isn't the
 * case), so this table should thus contain all command-line options.
 *
 * Each option in this array has four elements:
 *
 * 1. the long option string
 * 2. argument behavior for the option:
 *    no_argument - no argument permitted
 *    required_argument - an argument is expected
 *    optional_argument - an argument is permitted but not required
 * 3. this is a pointer to an int which is set to the 4th entry of the
 *    array if the option is present; or NULL, in which case
 *    getopt_long() returns the 4th entry
 * 4. the return value for getopt_long() when this long option (or the
 *    value to set the 3rd entry to; see #3)
 *
 * If you add something here, you should add it in src/main/usage.h
 * also, to document it.
 *
 * If you add something that has a short option equivalent, you should
 * add it to the getopt_long() call in parseOptions().
 */
static struct option cmdlineOptions[] = {
  // name, has_arg, *flag, val
  { "verbose"    , no_argument      , NULL, 'v'         },
  { "quiet"      , no_argument      , NULL, 'q'         },
  { "debug"      , required_argument, NULL, 'd'         },
  { "trace"      , required_argument, NULL, 't'         },
  { "stats"      , no_argument      , NULL, STATS       },
  { "no-checking", no_argument      , NULL, NO_CHECKING },
  { "show-config", no_argument      , NULL, SHOW_CONFIG },
  { "segv-nospin", no_argument      , NULL, SEGV_NOSPIN },
  { "help"       , no_argument      , NULL, 'h'         },
  { "version"    , no_argument      , NULL, 'V'         },
  { "about"      , no_argument      , NULL, 'V'         },
  { "lang"       , required_argument, NULL, 'L'         },
  { "parse-only" , no_argument      , NULL, PARSE_ONLY  },
  { "mmap"       , no_argument      , NULL, USE_MMAP    },
  { "strict-parsing", no_argument   , NULL, STRICT_PARSING },
  { "default-expr-depth", required_argument, NULL, DEFAULT_EXPR_DEPTH },
  { "print-expr-types", no_argument , NULL, PRINT_EXPR_TYPES },
  { "uf"         , required_argument, NULL, UF_THEORY },
  { NULL         , no_argument      , NULL, '\0'        }
};/* if you add things to the above, please remember to update usage.h! */

/** Full argv[0] */
const char *progPath;

/** Just the basename component of argv[0] */
const char *progName;

/** Parse argc/argv and put the result into a CVC4::Options struct. */
int parseOptions(int argc, char* argv[], CVC4::Options* opts)
throw(OptionException) {
  progPath = progName = argv[0];
  int c;

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL) {
    progName = x + 1;
  }
  opts->binary_name = string(progName);

  // The strange string in this call is the short option string.  The
  // initial '+' means that option processing stops as soon as a
  // non-option argument is encountered.  The initial ':' indicates
  // that getopt_long() should return ':' instead of '?' for a missing
  // option argument.  Then, each letter is a valid short option for
  // getopt_long(), and if it's encountered, getopt_long() returns
  // that character.  A ':' after an option character means an
  // argument is required; two colons indicates an argument is
  // optional; no colons indicate an argument is not permitted.
  // cmdlineOptions specifies all the long-options and the return
  // value for getopt_long() should they be encountered.
  while((c = getopt_long(argc, argv,
                         "+:hVvqL:d:t:",
                         cmdlineOptions, NULL)) != -1) {
    switch(c) {

    case 'h':
      printf(usage, opts->binary_name.c_str());
      exit(1);

    case 'V':
      fputs(Configuration::about().c_str(), stdout);
      exit(0);

    case 'v':
      ++opts->verbosity;
      break;

    case 'q':
      --opts->verbosity;
      break;

    case 'L':
      if(!strcmp(optarg, "cvc4") || !strcmp(optarg, "pl")) {
        opts->lang = parser::LANG_CVC4;
        break;
      } else if(!strcmp(optarg, "smtlib") || !strcmp(optarg, "smt")) {
        opts->lang = parser::LANG_SMTLIB;
        break;
      } else if(!strcmp(optarg, "smtlib2") || !strcmp(optarg, "smt2")) {
        opts->lang = parser::LANG_SMTLIB_V2;
        break;
      } else if(!strcmp(optarg, "auto")) {
        opts->lang = parser::LANG_AUTO;
        break;
      }

      if(strcmp(optarg, "help")) {
        throw OptionException(string("unknown language for --lang: `") +
                              optarg + "'.  Try --lang help.");
      }

      fputs(lang_help, stdout);
      exit(1);

    case 't':
      Trace.on(optarg);
      break;

    case 'd':
      Debug.on(optarg);
      Trace.on(optarg);
      break;

    case STATS:
      opts->statistics = true;
      break;

    case SEGV_NOSPIN:
      segvNoSpin = true;
      break;

    case PARSE_ONLY:
      opts->parseOnly = true;
      break;

    case NO_CHECKING:
      opts->semanticChecks = false;
      break;

    case USE_MMAP:
      opts->memoryMap = true;
      break;

    case STRICT_PARSING:
      opts->strictParsing = true;
      break;

    case DEFAULT_EXPR_DEPTH:
      {
        int depth = atoi(optarg);
        Debug.getStream() << Expr::setdepth(depth);
        Trace.getStream() << Expr::setdepth(depth);
        Notice.getStream() << Expr::setdepth(depth);
        Chat.getStream() << Expr::setdepth(depth);
        Message.getStream() << Expr::setdepth(depth);
        Warning.getStream() << Expr::setdepth(depth);
      }
      break;

    case PRINT_EXPR_TYPES:
      {
        Debug.getStream() << Expr::printtypes(true);
        Trace.getStream() << Expr::printtypes(true);
        Notice.getStream() << Expr::printtypes(true);
        Chat.getStream() << Expr::printtypes(true);
        Message.getStream() << Expr::printtypes(true);
        Warning.getStream() << Expr::printtypes(true);
      }
      break;

    case UF_THEORY:
      {
        if(!strcmp(optarg, "tim")) {
          opts->uf_implementation = Options::TIM;
        } else if(!strcmp(optarg, "morgan")) {
          opts->uf_implementation = Options::MORGAN;
        } else if(!strcmp(optarg, "help")) {
          printf("UF implementations available:\n");
          printf("tim\n");
          printf("morgan\n");
          exit(1);
        } else {
          throw OptionException(string("unknown option for --uf: `") +
                                optarg + "'.  Try --uf help.");
        }
      }
      break;

    case SHOW_CONFIG:
      fputs(Configuration::about().c_str(), stdout);
      printf("\n");
      printf("version   : %s\n", Configuration::getVersionString().c_str());
      printf("\n");
      printf("library   : %u.%u.%u\n",
             Configuration::getVersionMajor(),
             Configuration::getVersionMinor(),
             Configuration::getVersionRelease());
      printf("\n");
      printf("debug code : %s\n", Configuration::isDebugBuild() ? "yes" : "no");
      printf("tracing    : %s\n", Configuration::isTracingBuild() ? "yes" : "no");
      printf("muzzled    : %s\n", Configuration::isMuzzledBuild() ? "yes" : "no");
      printf("assertions : %s\n", Configuration::isAssertionBuild() ? "yes" : "no");
      printf("coverage   : %s\n", Configuration::isCoverageBuild() ? "yes" : "no");
      printf("profiling  : %s\n", Configuration::isProfilingBuild() ? "yes" : "no");
      printf("competition: %s\n", Configuration::isCompetitionBuild() ? "yes" : "no");
      exit(0);

    case '?':
      throw OptionException(string("can't understand option `") + argv[optind - 1] + "'");

    case ':':
      throw OptionException(string("option `") + argv[optind - 1] + "' missing its required argument");

    default:
      throw OptionException(string("can't understand option:") + argv[optind - 1] + "'");
    }

  }

  return optind;
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
