/*********************                                                        */
/*! \file options.cpp
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

#include "expr/expr.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/language.h"
#include "util/options.h"
#include "util/output.h"

#include "cvc4autoconfig.h"

using namespace std;
using namespace CVC4;

namespace CVC4 {

static const string optionsDescription = "\
   --lang | -L            force input language (default is `auto'; see --lang help)\n\
   --version | -V         identify this CVC4 binary\n\
   --help | -h            this command line reference\n\
   --parse-only           exit after parsing input\n\
   --mmap                 memory map file input\n\
   --show-config          show CVC4 static configuration\n\
   --segv-nospin          don't spin on segfault waiting for gdb\n\
   --lazy-type-checking   type check expressions only when necessary (default)\n\
   --eager-type-checking  type check expressions immediately on creation\n\
   --no-type-checking     never type check expressions\n\
   --no-checking          disable ALL semantic checks, including type checks \n\
   --no-theory-registration disable theory reg (not safe for some theories)\n\
   --strict-parsing       fail on non-conformant inputs (SMT2 only)\n\
   --verbose | -v         increase verbosity (repeatable)\n\
   --quiet | -q           decrease verbosity (repeatable)\n\
   --trace | -t           tracing for something (e.g. --trace pushpop)\n\
   --debug | -d           debugging for something (e.g. --debug arith), implies -t\n\
   --stats                give statistics on exit\n\
   --default-expr-depth=N print exprs to depth N (0 == default, -1 == no limit)\n\
   --print-expr-types     print types with variables when printing exprs\n\
   --uf=morgan|tim        select uninterpreted function theory implementation\n\
   --interactive          run interactively\n\
   --no-interactive       do not run interactively\n\
   --produce-models       support the get-value command\n\
   --produce-assignments  support the get-assignment command\n\
   --lazy-definition-expansion expand define-fun lazily\n\
   --rewrite-arithmetic-equalities rewrite (= x y) to (and (<= x y) (>= x y)) in arithmetic \n\
   --incremental          enable incremental solving\n";

static const string languageDescription = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto           attempt to automatically determine the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
";

string Options::getDescription() const {
  return optionsDescription;
}

void Options::printUsage(const std::string msg, std::ostream& out) {
  out << msg << optionsDescription << endl << flush;
  // printf(usage + options.getDescription(), options.binary_name.c_str());
  //     printf(usage, binary_name.c_str());
}

void Options::printLanguageHelp(std::ostream& out) {
  out << languageDescription << flush;
}

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
  NO_THEORY_REGISTRATION,
  USE_MMAP,
  SHOW_CONFIG,
  STRICT_PARSING,
  DEFAULT_EXPR_DEPTH,
  PRINT_EXPR_TYPES,
  UF_THEORY,
  LAZY_DEFINITION_EXPANSION,
  INTERACTIVE,
  NO_INTERACTIVE,
  PRODUCE_MODELS,
  PRODUCE_ASSIGNMENTS,
  NO_TYPE_CHECKING,
  LAZY_TYPE_CHECKING,
  EAGER_TYPE_CHECKING,
  INCREMENTAL,
  PIVOT_RULE,
  REWRITE_ARITHMETIC_EQUALITIES
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
  { "no-theory-registration", no_argument, NULL, NO_THEORY_REGISTRATION },
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
  { "lazy-definition-expansion", no_argument, NULL, LAZY_DEFINITION_EXPANSION },
  { "interactive", no_argument      , NULL, INTERACTIVE },
  { "no-interactive", no_argument   , NULL, NO_INTERACTIVE },
  { "produce-models", no_argument   , NULL, PRODUCE_MODELS},
  { "produce-assignments", no_argument, NULL, PRODUCE_ASSIGNMENTS},
  { "no-type-checking", no_argument, NULL, NO_TYPE_CHECKING},
  { "lazy-type-checking", no_argument, NULL, LAZY_TYPE_CHECKING},
  { "eager-type-checking", no_argument, NULL, EAGER_TYPE_CHECKING},
  { "incremental", no_argument, NULL, INCREMENTAL},
  { "pivot-rule" , required_argument, NULL, PIVOT_RULE  },
  { "rewrite-arithmetic-equalities" , no_argument, NULL, REWRITE_ARITHMETIC_EQUALITIES},
  { NULL         , no_argument      , NULL, '\0'        }
};/* if you add things to the above, please remember to update usage.h! */


/** Parse argc/argv and put the result into a CVC4::Options struct. */
int Options::parseOptions(int argc, char* argv[])
throw(OptionException) {
  const char *progName = argv[0];
  int c;

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL) {
    progName = x + 1;
  }
  binary_name = string(progName);

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
      help = true;
      break;
      // options.printUsage(usage);
      // exit(1);

    case 'V':
      version = true;
      break;
      // fputs(Configuration::about().c_str(), stdout);
      // exit(0);

    case 'v':
      ++verbosity;
      break;

    case 'q':
      --verbosity;
      break;

    case 'L':
      if(!strcmp(optarg, "cvc4") || !strcmp(optarg, "pl")) {
        inputLanguage = language::input::LANG_CVC4;
        break;
      } else if(!strcmp(optarg, "smtlib") || !strcmp(optarg, "smt")) {
        inputLanguage = language::input::LANG_SMTLIB;
        break;
      } else if(!strcmp(optarg, "smtlib2") || !strcmp(optarg, "smt2")) {
        inputLanguage = language::input::LANG_SMTLIB_V2;
        break;
      } else if(!strcmp(optarg, "auto")) {
        inputLanguage = language::input::LANG_AUTO;
        break;
      }

      if(strcmp(optarg, "help")) {
        throw OptionException(string("unknown language for --lang: `") +
                              optarg + "'.  Try --lang help.");
      }

      languageHelp = true;
      break;

    case 't':
      Trace.on(optarg);
      break;

    case 'd':
      Debug.on(optarg);
      Trace.on(optarg);
      break;

    case STATS:
      statistics = true;
      break;

    case SEGV_NOSPIN:
      segvNoSpin = true;
      break;

    case PARSE_ONLY:
      parseOnly = true;
      break;

    case NO_THEORY_REGISTRATION:
      theoryRegistration = false;
      break;

    case NO_CHECKING:
      semanticChecks = false;
      typeChecking = false;
      earlyTypeChecking = false;
      break;

    case USE_MMAP:
      memoryMap = true;
      break;

    case STRICT_PARSING:
      strictParsing = true;
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
          uf_implementation = Options::TIM;
        } else if(!strcmp(optarg, "morgan")) {
          uf_implementation = Options::MORGAN;
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

    case LAZY_DEFINITION_EXPANSION:
      lazyDefinitionExpansion = true;
      break;

    case INTERACTIVE:
      interactive = true;
      interactiveSetByUser = true;
      break;

    case NO_INTERACTIVE:
      interactive = false;
      interactiveSetByUser = true;
      break;

    case PRODUCE_MODELS:
      produceModels = true;
      break;

    case PRODUCE_ASSIGNMENTS:
      produceAssignments = true;
      break;

    case NO_TYPE_CHECKING:
      typeChecking = false;
      earlyTypeChecking = false;
      break;

    case LAZY_TYPE_CHECKING:
      typeChecking = true;
      earlyTypeChecking = false;
      break;

    case EAGER_TYPE_CHECKING:
      typeChecking = true;
      earlyTypeChecking = true;
      break;

    case INCREMENTAL:
      incrementalSolving = true;
      break;

    case REWRITE_ARITHMETIC_EQUALITIES:
      rewriteArithEqualities = true;
      break;

    case PIVOT_RULE:
      if(!strcmp(optarg, "min")) {
        pivotRule = MINIMUM;
        break;
      } else if(!strcmp(optarg, "min-break-ties")) {
        pivotRule = BREAK_TIES;
        break;
      } else if(!strcmp(optarg, "max")) {
        pivotRule = MAXIMUM;
        break;
      } else if(!strcmp(optarg, "help")) {
        printf("Pivot rules available:\n");
        printf("min\n");
        printf("min-break-ties\n");
        printf("max\n");
        exit(1);
      } else {
        throw OptionException(string("unknown option for --pivot-rule: `") +
                              optarg + "'.  Try --pivot-rule help.");
      }
      break;

    case SHOW_CONFIG:
      fputs(Configuration::about().c_str(), stdout);
      printf("\n");
      printf("version    : %s\n", Configuration::getVersionString().c_str());
      printf("\n");
      printf("library    : %u.%u.%u\n",
             Configuration::getVersionMajor(),
             Configuration::getVersionMinor(),
             Configuration::getVersionRelease());
      printf("\n");
      printf("debug code : %s\n", Configuration::isDebugBuild() ? "yes" : "no");
      printf("statistics : %s\n", Configuration::isStatisticsBuild() ? "yes" : "no");
      printf("tracing    : %s\n", Configuration::isTracingBuild() ? "yes" : "no");
      printf("muzzled    : %s\n", Configuration::isMuzzledBuild() ? "yes" : "no");
      printf("assertions : %s\n", Configuration::isAssertionBuild() ? "yes" : "no");
      printf("coverage   : %s\n", Configuration::isCoverageBuild() ? "yes" : "no");
      printf("profiling  : %s\n", Configuration::isProfilingBuild() ? "yes" : "no");
      printf("competition: %s\n", Configuration::isCompetitionBuild() ? "yes" : "no");
      printf("\n");
      printf("cudd       : %s\n", Configuration::isBuiltWithCudd() ? "yes" : "no");
      printf("cln        : %s\n", Configuration::isBuiltWithCln() ? "yes" : "no");
      printf("gmp        : %s\n", Configuration::isBuiltWithGmp() ? "yes" : "no");
      printf("tls        : %s\n", Configuration::isBuiltWithTlsSupport() ? "yes" : "no");
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

bool Options::rewriteArithEqualities = false;

}/* CVC4 namespace */
