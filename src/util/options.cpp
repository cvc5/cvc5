/*********************                                                        */
/*! \file options.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway, taking
 ** Minor contributors (to current version): barrett, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

CVC4_THREADLOCAL(const Options*) Options::s_current = NULL;

#ifdef CVC4_DEBUG
#  define USE_EARLY_TYPE_CHECKING_BY_DEFAULT true
#else /* CVC4_DEBUG */
#  define USE_EARLY_TYPE_CHECKING_BY_DEFAULT false
#endif /* CVC4_DEBUG */

#if defined(CVC4_MUZZLED) || defined(CVC4_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC4_MUZZLED || CVC4_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC4_MUZZLED || CVC4_COMPETITION_MODE */

Options::Options() :
  binary_name(),
  statistics(false),
  in(&std::cin),
  out(&std::cout),
  err(&std::cerr),
  verbosity(0),
  inputLanguage(language::input::LANG_AUTO),
  outputLanguage(language::output::LANG_AUTO),
  parseOnly(false),
  preprocessOnly(false),
  semanticChecks(DO_SEMANTIC_CHECKS_BY_DEFAULT),
  theoryRegistration(true),
  memoryMap(false),
  strictParsing(false),
  lazyDefinitionExpansion(false),
  simplificationMode(SIMPLIFICATION_MODE_BATCH),
  doStaticLearning(true),
  interactive(false),
  interactiveSetByUser(false),
  segvNoSpin(false),
  produceModels(false),
  produceAssignments(false),
  typeChecking(DO_SEMANTIC_CHECKS_BY_DEFAULT),
  earlyTypeChecking(USE_EARLY_TYPE_CHECKING_BY_DEFAULT),
  incrementalSolving(false),
  replayFilename(""),
  replayStream(NULL),
  replayLog(NULL),
  variableRemovalEnabled(false),
  arithPropagation(true),
  satRandomFreq(0.0),
  satRandomSeed(91648253),// Minisat's default value
  pivotRule(MINIMUM),
  arithPivotThreshold(16),
  arithPropagateMaxLength(16),
  ufSymmetryBreaker(true)
{
}

static const string optionsDescription = "\
   --lang | -L            force input language (default is `auto'; see --lang help)\n\
   --output-lang          force output language (default is `auto'; see --lang help)\n\
   --version | -V         identify this CVC4 binary\n\
   --help | -h            this command line reference\n\
   --parse-only           exit after parsing input\n\
   --preprocess-only      exit after preprocessing (useful with --stats or --dump)\n\
   --dump=MODE            dump preprocessed assertions, T-propagations, etc., see --dump=help\n\
   --dump-to=FILE         all dumping goes to FILE (instead of stdout)\n\
   --mmap                 memory map file input\n\
   --show-config          show CVC4 static configuration\n\
   --segv-nospin          don't spin on segfault waiting for gdb\n\
   --lazy-type-checking   type check expressions only when necessary (default)\n\
   --eager-type-checking  type check expressions immediately on creation (debug builds only)\n\
   --no-type-checking     never type check expressions\n\
   --no-checking          disable ALL semantic checks, including type checks\n\
   --no-theory-registration disable theory reg (not safe for some theories)\n\
   --strict-parsing       fail on non-conformant inputs (SMT2 only)\n\
   --verbose | -v         increase verbosity (may be repeated)\n\
   --quiet | -q           decrease verbosity (may be repeated)\n\
   --trace | -t           trace something (e.g. -t pushpop), can repeat\n\
   --debug | -d           debug something (e.g. -d arith), can repeat\n\
   --show-debug-tags      show all avalable tags for debugging\n\
   --show-trace-tags      show all avalable tags for tracing\n\
   --stats                give statistics on exit\n\
   --default-expr-depth=N print exprs to depth N (0 == default, -1 == no limit)\n\
   --print-expr-types     print types with variables when printing exprs\n\
   --interactive          run interactively\n\
   --no-interactive       do not run interactively\n\
   --produce-models | -m  support the get-value command\n\
   --produce-assignments  support the get-assignment command\n\
   --lazy-definition-expansion expand define-fun lazily\n\
   --simplification=MODE  choose simplification mode, see --simplification=help\n\
   --no-static-learning   turn off static learning (e.g. diamond-breaking)\n\
   --replay=file          replay decisions from file\n\
   --replay-log=file      log decisions and propagations to file\n\
   --pivot-rule=RULE      change the pivot rule (see --pivot-rule help)\n\
   --pivot-threshold=N   sets the number of heuristic pivots per variable per simplex instance\n\
   --prop-row-length=N    sets the maximum row length to be used in propagation\n\
   --random-freq=P        sets the frequency of random decisions in the sat solver(P=0.0 by default)\n\
   --random-seed=S        sets the random seed for the sat solver\n\
   --disable-variable-removal enable permanent removal of variables in arithmetic (UNSAFE! experts only)\n\
   --disable-arithmetic-propagation turns on arithmetic propagation\n\
   --disable-symmetry-breaker turns off UF symmetry breaker (Deharbe et al., CADE 2011)\n\
   --incremental | -i     enable incremental solving\n\
   --time-limit=MS        enable time limiting (give milliseconds)\n\
   --time-limit-per=MS    enable time limiting per query (give milliseconds)\n\
   --limit=N              enable resource limiting\n\
   --limit-per=N          enable resource limiting per query\n";

#warning "Change CL options as --disable-variable-removal cannot do anything currently."

static const string languageDescription = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto           attempt to automatically determine the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
\n\
Languages currently supported as arguments to the --output-lang option:\n\
  auto           match the output language to the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
  ast            internal format (simple syntax-tree language)\n\
";

static const string simplificationHelp = "\
Simplification modes currently supported by the --simplification option:\n\
\n\
batch (default) \n\
+ save up all ASSERTions; run nonclausal simplification and clausal\n\
  (MiniSat) propagation for all of them only after reaching a querying command\n\
  (CHECKSAT or QUERY or predicate SUBTYPE declaration)\n\
\n\
incremental\n\
+ run nonclausal simplification and clausal propagation at each ASSERT\n\
  (and at CHECKSAT/QUERY/SUBTYPE)\n\
\n\
none\n\
+ do not perform nonclausal simplification\n\
";

static const string dumpHelp = "\
Dump modes currently supported by the --dump option:\n\
\n\
benchmark\n\
+ Dump the benchmark structure (set-logic, push/pop, queries, etc.), but\n\
  does not include any declarations or assertions.  Implied by all following\n\
  modes.\n\
\n\
declarations\n\
+ Dump declarations.  Implied by all following modes.\n\
\n\
assertions\n\
+ Output the assertions after non-clausal simplification and static\n\
  learning phases, but before presolve-time T-lemmas arrive.  If\n\
  non-clausal simplification and static learning are off\n\
  (--simplification=none --no-static-learning), the output\n\
  will closely resemble the input (with term-level ITEs removed).\n\
\n\
learned\n\
+ Output the assertions after non-clausal simplification, static\n\
  learning, and presolve-time T-lemmas.  This should include all eager\n\
  T-lemmas (in the form provided by the theory, which my or may not be\n\
  clausal).  Also includes level-0 BCP done by Minisat.\n\
\n\
clauses\n\
+ Do all the preprocessing outlined above, and dump the CNF-converted\n\
  output\n\
\n\
state\n\
+ Dump all contextual assertions (e.g., SAT decisions, propagations..).\n\
  Implied by all \"stateful\" modes below and conflicts with all\n\
  non-stateful modes below.\n\
\n\
t-conflicts [non-stateful]\n\
+ Output correctness queries for all theory conflicts\n\
\n\
missed-t-conflicts [stateful]\n\
+ Output completeness queries for theory conflicts\n\
\n\
t-propagations [stateful]\n\
+ Output correctness queries for all theory propagations\n\
\n\
missed-t-propagations [stateful]\n\
+ Output completeness queries for theory propagations (LARGE and EXPENSIVE)\n\
\n\
t-lemmas [non-stateful]\n\
+ Output correctness queries for all theory lemmas\n\
\n\
t-explanations [non-stateful]\n\
+ Output correctness queries for all theory explanations\n\
\n\
Dump modes can be combined with multiple uses of --dump.  Generally you want\n\
one from the assertions category (either asertions, learned, or clauses), and\n\
perhaps one or more stateful or non-stateful modes for checking correctness\n\
and completeness of decision procedure implementations.  Stateful modes dump\n\
the contextual assertions made by the core solver (all decisions and propagations\n\
as assertions; that affects the validity of the resulting correctness and\n\
completeness queries, so of course stateful and non-stateful modes cannot\n\
be mixed in the same run.\n\
\n\
The --output-language option controls the language used for dumping, and\n\
this allows you to connect CVC4 to another solver implementation via a UNIX\n\
pipe to perform on-line checking.  The --dump-to option can be used to dump\n\
to a file.\n\
";

string Options::getDescription() const {
  return optionsDescription;
}

void Options::printUsage(const std::string msg, std::ostream& out) {
  out << msg << optionsDescription << endl << flush;
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
  SMTCOMP = 256, /* avoid clashing with char options */
  STATS,
  SEGV_NOSPIN,
  OUTPUT_LANGUAGE,
  PARSE_ONLY,
  PREPROCESS_ONLY,
  DUMP,
  DUMP_TO,
  NO_CHECKING,
  NO_THEORY_REGISTRATION,
  USE_MMAP,
  SHOW_DEBUG_TAGS,
  SHOW_TRACE_TAGS,
  SHOW_CONFIG,
  STRICT_PARSING,
  DEFAULT_EXPR_DEPTH,
  PRINT_EXPR_TYPES,
  UF_THEORY,
  LAZY_DEFINITION_EXPANSION,
  SIMPLIFICATION_MODE,
  NO_STATIC_LEARNING,
  INTERACTIVE,
  NO_INTERACTIVE,
  PRODUCE_ASSIGNMENTS,
  NO_TYPE_CHECKING,
  LAZY_TYPE_CHECKING,
  EAGER_TYPE_CHECKING,
  REPLAY,
  REPLAY_LOG,
  PIVOT_RULE,
  RANDOM_FREQUENCY,
  RANDOM_SEED,
  ARITHMETIC_VARIABLE_REMOVAL,
  ARITHMETIC_PROPAGATION,
  ARITHMETIC_PIVOT_THRESHOLD,
  ARITHMETIC_PROP_MAX_LENGTH,
  DISABLE_SYMMETRY_BREAKER,
  TIME_LIMIT,
  TIME_LIMIT_PER,
  LIMIT,
  LIMIT_PER
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
  { "show-debug-tags", no_argument  , NULL, SHOW_DEBUG_TAGS },
  { "show-trace-tags", no_argument  , NULL, SHOW_TRACE_TAGS },
  { "show-config", no_argument      , NULL, SHOW_CONFIG },
  { "segv-nospin", no_argument      , NULL, SEGV_NOSPIN },
  { "help"       , no_argument      , NULL, 'h'         },
  { "version"    , no_argument      , NULL, 'V'         },
  { "about"      , no_argument      , NULL, 'V'         },
  { "lang"       , required_argument, NULL, 'L'         },
  { "output-lang", required_argument, NULL, OUTPUT_LANGUAGE },
  { "parse-only" , no_argument      , NULL, PARSE_ONLY  },
  { "preprocess-only", no_argument      , NULL, PREPROCESS_ONLY },
  { "dump"       , required_argument, NULL, DUMP        },
  { "dump-to"    , required_argument, NULL, DUMP_TO     },
  { "mmap"       , no_argument      , NULL, USE_MMAP    },
  { "strict-parsing", no_argument   , NULL, STRICT_PARSING },
  { "default-expr-depth", required_argument, NULL, DEFAULT_EXPR_DEPTH },
  { "print-expr-types", no_argument , NULL, PRINT_EXPR_TYPES },
  { "uf"         , required_argument, NULL, UF_THEORY   },
  { "lazy-definition-expansion", no_argument, NULL, LAZY_DEFINITION_EXPANSION },
  { "simplification", required_argument, NULL, SIMPLIFICATION_MODE },
  { "no-static-learning", no_argument, NULL, NO_STATIC_LEARNING },
  { "interactive", no_argument      , NULL, INTERACTIVE },
  { "no-interactive", no_argument   , NULL, NO_INTERACTIVE },
  { "produce-models", no_argument   , NULL, 'm' },
  { "produce-assignments", no_argument, NULL, PRODUCE_ASSIGNMENTS },
  { "no-type-checking", no_argument , NULL, NO_TYPE_CHECKING },
  { "lazy-type-checking", no_argument, NULL, LAZY_TYPE_CHECKING },
  { "eager-type-checking", no_argument, NULL, EAGER_TYPE_CHECKING },
  { "incremental", no_argument      , NULL, 'i' },
  { "replay"     , required_argument, NULL, REPLAY      },
  { "replay-log" , required_argument, NULL, REPLAY_LOG  },
  { "pivot-rule" , required_argument, NULL, PIVOT_RULE  },
  { "pivot-threshold" , required_argument, NULL, ARITHMETIC_PIVOT_THRESHOLD  },
  { "prop-row-length" , required_argument, NULL, ARITHMETIC_PROP_MAX_LENGTH  },
  { "random-freq" , required_argument, NULL, RANDOM_FREQUENCY  },
  { "random-seed" , required_argument, NULL, RANDOM_SEED  },
  { "disable-variable-removal", no_argument, NULL, ARITHMETIC_VARIABLE_REMOVAL },
  { "disable-arithmetic-propagation", no_argument, NULL, ARITHMETIC_PROPAGATION },
  { "disable-symmetry-breaker", no_argument, NULL, DISABLE_SYMMETRY_BREAKER },
  { "time-limit" , required_argument, NULL, TIME_LIMIT  },
  { "time-limit-per", required_argument, NULL, TIME_LIMIT_PER },
  { "limit"      , required_argument, NULL, LIMIT       },
  { "limit-per"  , required_argument, NULL, LIMIT_PER   },
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

  // The strange string in this call is the short option string.  An
  // initial '+' means that option processing stops as soon as a
  // non-option argument is encountered (it is not present, by design).
  // The initial ':' indicates that getopt_long() should return ':'
  // instead of '?' for a missing option argument.  Then, each letter
  // is a valid short option for getopt_long(), and if it's encountered,
  // getopt_long() returns that character.  A ':' after an option
  // character means an argument is required; two colons indicates an
  // argument is optional; no colons indicate an argument is not
  // permitted.  cmdlineOptions specifies all the long-options and the
  // return value for getopt_long() should they be encountered.
  while((c = getopt_long(argc, argv,
                         ":himVvqL:d:t:",
                         cmdlineOptions, NULL)) != -1) {
    switch(c) {

    case 'h':
      help = true;
      break;

    case 'V':
      version = true;
      break;

    case 'v':
      ++verbosity;
      break;

    case 'q':
      --verbosity;
      break;

    case 'L':
      setInputLanguage(optarg);
      break;

    case OUTPUT_LANGUAGE:
      setOutputLanguage(optarg);
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

    case PREPROCESS_ONLY:
      preprocessOnly = true;
      break;

    case DUMP: {
#ifdef CVC4_DUMPING
      char* tokstr = optarg;
      char* toksave;
      while((optarg = strtok_r(tokstr, ",", &toksave)) != NULL) {
        tokstr = NULL;
        if(!strcmp(optarg, "benchmark")) {
        } else if(!strcmp(optarg, "declarations")) {
        } else if(!strcmp(optarg, "assertions")) {
        } else if(!strcmp(optarg, "learned")) {
        } else if(!strcmp(optarg, "clauses")) {
        } else if(!strcmp(optarg, "t-conflicts") ||
                  !strcmp(optarg, "t-lemmas") ||
                  !strcmp(optarg, "t-explanations")) {
          // These are "non-state-dumping" modes.  If state (SAT decisions,
          // propagations, etc.) is dumped, it will interfere with the validity
          // of these generated queries.
          if(Dump.isOn("state")) {
            throw OptionException(string("dump option `") + optarg +
                                  "' conflicts with a previous, "
                                  "state-dumping dump option.  You cannot "
                                  "mix stateful and non-stateful dumping modes; "
                                  "see --dump help.");
          } else {
            Dump.on("no-permit-state");
          }
        } else if(!strcmp(optarg, "state") ||
                  !strcmp(optarg, "missed-t-conflicts") ||
                  !strcmp(optarg, "t-propagations") ||
                  !strcmp(optarg, "missed-t-propagations")) {
          // These are "state-dumping" modes.  If state (SAT decisions,
          // propagations, etc.) is not dumped, it will interfere with the
          // validity of these generated queries.
          if(Dump.isOn("no-permit-state")) {
            throw OptionException(string("dump option `") + optarg +
                                  "' conflicts with a previous, "
                                  "non-state-dumping dump option.  You cannot "
                                  "mix stateful and non-stateful dumping modes; "
                                  "see --dump help.");
          } else {
            Dump.on("state");
          }
        } else if(!strcmp(optarg, "help")) {
          puts(dumpHelp.c_str());
          exit(1);
        } else {
          throw OptionException(string("unknown option for --dump: `") +
                                optarg + "'.  Try --dump help.");
        }

        Dump.on(optarg);
        Dump.on("benchmark");
        if(strcmp(optarg, "benchmark")) {
          Dump.on("declarations");
        }
      }
#else /* CVC4_DUMPING */
      throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
      break;
    }

    case DUMP_TO: {
#ifdef CVC4_DUMPING
      if(optarg == NULL || *optarg == '\0') {
        throw OptionException(string("Bad file name for --dump-to"));
      } else if(!strcmp(optarg, "-")) {
        Dump.setStream(DumpC::dump_cout);
      } else {
        ostream* dumpTo = new ofstream(optarg, ofstream::out | ofstream::trunc);
        if(!*dumpTo) {
          throw OptionException(string("Cannot open dump-to file (maybe it exists): `") + optarg + "'");
        }
        Dump.setStream(*dumpTo);
      }
#else /* CVC4_DUMPING */
      throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
    }
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

    case LAZY_DEFINITION_EXPANSION:
      lazyDefinitionExpansion = true;
      break;

    case SIMPLIFICATION_MODE:
      if(!strcmp(optarg, "batch")) {
        simplificationMode = SIMPLIFICATION_MODE_BATCH;
      } else if(!strcmp(optarg, "incremental")) {
        simplificationMode = SIMPLIFICATION_MODE_INCREMENTAL;
      } else if(!strcmp(optarg, "none")) {
        simplificationMode = SIMPLIFICATION_MODE_NONE;
      } else if(!strcmp(optarg, "help")) {
        puts(simplificationHelp.c_str());
        exit(1);
      } else {
        throw OptionException(string("unknown option for --simplification: `") +
                              optarg + "'.  Try --simplification help.");
      }
      break;

    case NO_STATIC_LEARNING:
      doStaticLearning = false;
      break;

    case INTERACTIVE:
      interactive = true;
      interactiveSetByUser = true;
      break;

    case NO_INTERACTIVE:
      interactive = false;
      interactiveSetByUser = true;
      break;

    case 'm':
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

    case 'i':
      incrementalSolving = true;
      break;

    case REPLAY:
#ifdef CVC4_REPLAY
      if(optarg == NULL || *optarg == '\0') {
        throw OptionException(string("Bad file name for --replay"));
      } else {
        replayFilename = optarg;
      }
#else /* CVC4_REPLAY */
      throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
      break;

    case REPLAY_LOG:
#ifdef CVC4_REPLAY
      if(optarg == NULL || *optarg == '\0') {
        throw OptionException(string("Bad file name for --replay-log"));
      } else if(!strcmp(optarg, "-")) {
        replayLog = &cout;
      } else {
        replayLog = new ofstream(optarg, ofstream::out | ofstream::trunc);
        if(!*replayLog) {
          throw OptionException(string("Cannot open replay-log file: `") + optarg + "'");
        }
      }
#else /* CVC4_REPLAY */
      throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
      break;

    case ARITHMETIC_VARIABLE_REMOVAL:
      variableRemovalEnabled = false;
      break;

    case ARITHMETIC_PROPAGATION:
      arithPropagation = false;
      break;

    case DISABLE_SYMMETRY_BREAKER:
      ufSymmetryBreaker = false;
      break;

    case TIME_LIMIT:
      {
        int i = atoi(optarg);
        if(i < 0) {
          throw OptionException("--time-limit requires a nonnegative argument.");
        }
        cumulativeMillisecondLimit = (unsigned long) i;
      }
      break;
    case TIME_LIMIT_PER:
      {
        int i = atoi(optarg);
        if(i < 0) {
          throw OptionException("--time-limit-per requires a nonnegative argument.");
        }
        perCallMillisecondLimit = (unsigned long) i;
      }
      break;
    case LIMIT:
      {
        int i = atoi(optarg);
        if(i < 0) {
          throw OptionException("--limit requires a nonnegative argument.");
        }
        cumulativeResourceLimit = (unsigned long) i;
      }
      break;
    case LIMIT_PER:
      {
        int i = atoi(optarg);
        if(i < 0) {
          throw OptionException("--limit-per requires a nonnegative argument.");
        }
        perCallResourceLimit = (unsigned long) i;
        break;
      }

    case RANDOM_SEED:
      satRandomSeed = atof(optarg);
      break;

    case RANDOM_FREQUENCY:
      satRandomFreq = atof(optarg);
      if(! (0.0 <= satRandomFreq && satRandomFreq <= 1.0)){
        throw OptionException(string("--random-freq: `") +
                              optarg + "' is not between 0.0 and 1.0.");
      }
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

    case ARITHMETIC_PIVOT_THRESHOLD:
      arithPivotThreshold = atoi(optarg);
      break;

    case ARITHMETIC_PROP_MAX_LENGTH:
      arithPropagateMaxLength = atoi(optarg);
      break;

    case SHOW_DEBUG_TAGS:
      if(Configuration::isDebugBuild()) {
        printf("available tags:");
        unsigned ntags = Configuration::getNumDebugTags();
        char const* const* tags = Configuration::getDebugTags();
        for(unsigned i = 0; i < ntags; ++ i) {
          printf(" %s", tags[i]);
        }
        printf("\n");
      } else {
        throw OptionException("debug tags not available in non-debug build");
      }
      exit(0);
      break;

    case SHOW_TRACE_TAGS:
      if(Configuration::isTracingBuild()) {
        printf("available tags:");
        unsigned ntags = Configuration::getNumTraceTags();
        char const* const* tags = Configuration::getTraceTags();
        for (unsigned i = 0; i < ntags; ++ i) {
          printf(" %s", tags[i]);
        }
        printf("\n");
      } else {
        throw OptionException("trace tags not available in non-tracing build");
      }
      exit(0);
      break;

    case SHOW_CONFIG:
      fputs(Configuration::about().c_str(), stdout);
      printf("\n");
      printf("version    : %s\n", Configuration::getVersionString().c_str());
      if(Configuration::isSubversionBuild()) {
        printf("subversion : yes [%s r%u%s]\n",
               Configuration::getSubversionBranchName(),
               Configuration::getSubversionRevision(),
               Configuration::hasSubversionModifications() ?
                 " (with modifications)" : "");
      } else {
        printf("subversion : %s\n", Configuration::isSubversionBuild() ? "yes" : "no");
      }
      printf("\n");
      printf("library    : %u.%u.%u\n",
             Configuration::getVersionMajor(),
             Configuration::getVersionMinor(),
             Configuration::getVersionRelease());
      printf("\n");
      printf("debug code : %s\n", Configuration::isDebugBuild() ? "yes" : "no");
      printf("statistics : %s\n", Configuration::isStatisticsBuild() ? "yes" : "no");
      printf("replay     : %s\n", Configuration::isReplayBuild() ? "yes" : "no");
      printf("tracing    : %s\n", Configuration::isTracingBuild() ? "yes" : "no");
      printf("dumping    : %s\n", Configuration::isDumpingBuild() ? "yes" : "no");
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

    case ':':
      throw OptionException(string("option `") + argv[optind - 1] + "' missing its required argument");

    case '?':
    default:
      throw OptionException(string("can't understand option `") + argv[optind - 1] + "'");
    }
  }

  return optind;
}

void Options::setOutputLanguage(const char* str) throw(OptionException) {
  if(!strcmp(str, "cvc4") || !strcmp(str, "pl")) {
    outputLanguage = language::output::LANG_CVC4;
    return;
  } else if(!strcmp(str, "smtlib") || !strcmp(str, "smt")) {
    outputLanguage = language::output::LANG_SMTLIB;
    return;
  } else if(!strcmp(str, "smtlib2") || !strcmp(str, "smt2")) {
    outputLanguage = language::output::LANG_SMTLIB_V2;
    return;
  } else if(!strcmp(str, "ast")) {
    outputLanguage = language::output::LANG_AST;
    return;
  } else if(!strcmp(str, "auto")) {
    outputLanguage = language::output::LANG_AUTO;
    return;
  }

  if(strcmp(str, "help")) {
    throw OptionException(string("unknown language for --output-lang: `") +
                          str + "'.  Try --output-lang help.");
  }

  languageHelp = true;
}

void Options::setInputLanguage(const char* str) throw(OptionException) {
  if(!strcmp(str, "cvc4") || !strcmp(str, "pl") || !strcmp(str, "presentation")) {
    inputLanguage = language::input::LANG_CVC4;
    return;
  } else if(!strcmp(str, "smtlib") || !strcmp(str, "smt")) {
    inputLanguage = language::input::LANG_SMTLIB;
    return;
  } else if(!strcmp(str, "smtlib2") || !strcmp(str, "smt2")) {
    inputLanguage = language::input::LANG_SMTLIB_V2;
    return;
  } else if(!strcmp(str, "auto")) {
    inputLanguage = language::input::LANG_AUTO;
    return;
  }

  if(strcmp(str, "help")) {
    throw OptionException(string("unknown language for --lang: `") +
                          str + "'.  Try --lang help.");
  }

  languageHelp = true;
}

std::ostream& operator<<(std::ostream& out, Options::ArithPivotRule rule) {
  switch(rule) {
  case Options::MINIMUM:
    out << "MINIMUM";
    break;
  case Options::BREAK_TIES:
    out << "BREAK_TIES";
    break;
  case Options::MAXIMUM:
    out << "MAXIMUM";
    break;
  default:
    out << "ArithPivotRule!UNKNOWN";
  }

  return out;
}

#undef USE_EARLY_TYPE_CHECKING_BY_DEFAULT
#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}/* CVC4 namespace */
