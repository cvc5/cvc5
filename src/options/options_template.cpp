/*********************                                                        */
/*! \file options_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Contains code for handling command-line options.
 **
 ** Contains code for handling command-line options
 **/

#if !defined(_BSD_SOURCE) && defined(__MINGW32__) && !defined(__MINGW64__)
// force use of optreset; mingw32 croaks on argv-switching otherwise
#  include "cvc4autoconfig.h"
#  define _BSD_SOURCE
#  undef HAVE_DECL_OPTRESET
#  define HAVE_DECL_OPTRESET 1
#  define CVC4_IS_NOT_REALLY_BSD
#endif /* !_BSD_SOURCE && __MINGW32__ && !__MINGW64__ */

#ifdef __MINGW64__
extern int optreset;
#endif /* __MINGW64__ */

#include <getopt.h>

// clean up
#ifdef CVC4_IS_NOT_REALLY_BSD
#  undef _BSD_SOURCE
#endif /* CVC4_IS_NOT_REALLY_BSD */

#include <cstdio>
#include <cstdlib>
#include <new>
#include <string>
#include <sstream>
#include <limits>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include "expr/expr.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/language.h"
#include "util/tls.h"

${include_all_option_headers}

#line 57 "${template}"

#include "util/output.h"
#include "options/options_holder.h"
#include "cvc4autoconfig.h"
#include "options/base_options_handlers.h"

${option_handler_includes}

#line 66 "${template}"

using namespace CVC4;
using namespace CVC4::options;

namespace CVC4 {

CVC4_THREADLOCAL(Options*) Options::s_current = NULL;

/**
 * This is a default handler for options of built-in C++ type.  This
 * template is really just a helper for the handleOption() template,
 * below.  Variants of this template handle numeric and non-numeric,
 * integral and non-integral, signed and unsigned C++ types.
 * handleOption() makes sure to instantiate the right one.
 *
 * This implements default behavior when e.g. an option is
 * unsigned but the user specifies a negative argument; etc.
 */
template <class T, bool is_numeric, bool is_integer>
struct OptionHandler {
  static T handle(std::string option, std::string optionarg);
};/* struct OptionHandler<> */

/** Variant for integral C++ types */
template <class T>
struct OptionHandler<T, true, true> {
  static T handle(std::string option, std::string optionarg) {
    try {
      Integer i(optionarg, 10);

      if(! std::numeric_limits<T>::is_signed && i < 0) {
        // unsigned type but user gave negative argument
        throw OptionException(option + " requires a nonnegative argument");
      } else if(i < std::numeric_limits<T>::min()) {
        // negative overflow for type
        std::stringstream ss;
        ss << option << " requires an argument >= " << std::numeric_limits<T>::min();
        throw OptionException(ss.str());
      } else if(i > std::numeric_limits<T>::max()) {
        // positive overflow for type
        std::stringstream ss;
        ss << option << " requires an argument <= " << std::numeric_limits<T>::max();
        throw OptionException(ss.str());
      }

      if(std::numeric_limits<T>::is_signed) {
        return T(i.getLong());
      } else {
        return T(i.getUnsignedLong());
      }
    } catch(std::invalid_argument&) {
      // user gave something other than an integer
      throw OptionException(option + " requires an integer argument");
    }
  }
};/* struct OptionHandler<T, true, true> */

/** Variant for numeric but non-integral C++ types */
template <class T>
struct OptionHandler<T, true, false> {
  static T handle(std::string option, std::string optionarg) {
    std::stringstream in(optionarg);
    long double r;
    in >> r;
    if(! in.eof()) {
      // we didn't consume the whole string (junk at end)
      throw OptionException(option + " requires a numeric argument");
    }

    if(! std::numeric_limits<T>::is_signed && r < 0.0) {
      // unsigned type but user gave negative value
      throw OptionException(option + " requires a nonnegative argument");
    } else if(r < -std::numeric_limits<T>::max()) {
      // negative overflow for type
      std::stringstream ss;
      ss << option << " requires an argument >= " << -std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    } else if(r > std::numeric_limits<T>::max()) {
      // positive overflow for type
      std::stringstream ss;
      ss << option << " requires an argument <= " << std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    }

    return T(r);
  }
};/* struct OptionHandler<T, true, false> */

/** Variant for non-numeric C++ types */
template <class T>
struct OptionHandler<T, false, false> {
  static T handle(std::string option, std::string optionarg) {
    T::unsupported_handleOption_call___please_write_me;
    // The above line causes a compiler error if this version of the template
    // is ever instantiated (meaning that a specialization is missing).  So
    // don't worry about the segfault in the next line, the "return" is only
    // there to keep the compiler from giving additional, distracting errors
    // and warnings.
    return *(T*)0;
  }
};/* struct OptionHandler<T, false, false> */

/** Handle an option of type T in the default way. */
template <class T>
T handleOption(std::string option, std::string optionarg) {
  return OptionHandler<T, std::numeric_limits<T>::is_specialized, std::numeric_limits<T>::is_integer>::handle(option, optionarg);
}

/** Handle an option of type std::string in the default way. */
template <>
std::string handleOption<std::string>(std::string option, std::string optionarg) {
  return optionarg;
}

/**
 * Run handler, and any user-given predicates, for option T.
 * If a user specifies a :handler or :predicates, it overrides this.
 */
template <class T>
typename T::type runHandlerAndPredicates(T, std::string option, std::string optionarg, SmtEngine* smt) {
  // By default, parse the option argument in a way appropriate for its type.
  // E.g., for "unsigned int" options, ensure that the provided argument is
  // a nonnegative integer that fits in the unsigned int type.

  return handleOption<typename T::type>(option, optionarg);
}

template <class T>
void runBoolPredicates(T, std::string option, bool b, SmtEngine* smt) {
  // By default, nothing to do for bool.  Users add things with
  // :predicate in options files to provide custom checking routines
  // that can throw exceptions.
}

${all_custom_handlers}

#line 203 "${template}"

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
  d_holder(new options::OptionsHolder()) {
}

Options::Options(const Options& options) :
  d_holder(new options::OptionsHolder(*options.d_holder)) {
}

Options::~Options() {
  delete d_holder;
}

options::OptionsHolder::OptionsHolder() : ${all_modules_defaults}
{
}

#line 233 "${template}"

static const std::string mostCommonOptionsDescription = "\
Most commonly-used CVC4 options:${common_documentation}";

#line 238 "${template}"

static const std::string optionsDescription = mostCommonOptionsDescription + "\n\
\n\
Additional CVC4 options:${remaining_documentation}";

#line 244 "${template}"

static const std::string optionsFootnote = "\n\
[*] Each of these options has a --no-OPTIONNAME variant, which reverses the\n\
    sense of the option.\n\
";

static const std::string languageDescription = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto                           attempt to automatically determine language\n\
  cvc4 | presentation | pl       CVC4 presentation language\n\
  smt1 | smtlib1                 SMT-LIB format 1.2\n\
  smt | smtlib | smt2 | smtlib2  SMT-LIB format 2.0\n\
  tptp                           TPTP format (cnf and fof)\n\
\n\
Languages currently supported as arguments to the --output-lang option:\n\
  auto                           match output language to input language\n\
  cvc4 | presentation | pl       CVC4 presentation language\n\
  smt1 | smtlib1                 SMT-LIB format 1.2\n\
  smt | smtlib | smt2 | smtlib2  SMT-LIB format 2.0\n\
  tptp                           TPTP format\n\
  ast                            internal format (simple syntax trees)\n\
";

std::string Options::getDescription() const {
  return optionsDescription;
}

void Options::printUsage(const std::string msg, std::ostream& out) {
  out << msg << optionsDescription << std::endl
      << optionsFootnote << std::endl << std::flush;
}

void Options::printShortUsage(const std::string msg, std::ostream& out) {
  out << msg << mostCommonOptionsDescription << std::endl
      << optionsFootnote << std::endl
      << "For full usage, please use --help." << std::endl << std::endl << std::flush;
}

void Options::printLanguageHelp(std::ostream& out) {
  out << languageDescription << std::flush;
}

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
static struct option cmdlineOptions[] = {${all_modules_long_options}
  { NULL, no_argument, NULL, '\0' }
};/* cmdlineOptions */

#line 315 "${template}"

static void preemptGetopt(int& argc, char**& argv, const char* opt) {
  const size_t maxoptlen = 128;

  Debug("preemptGetopt") << "preempting getopt() with " << opt << std::endl;

  AlwaysAssert(opt != NULL && *opt != '\0');
  AlwaysAssert(strlen(opt) <= maxoptlen);

  ++argc;
  unsigned i = 1;
  while(argv[i] != NULL && argv[i][0] != '\0') {
    ++i;
  }

  if(argv[i] == NULL) {
    argv = (char**) realloc(argv, (i + 6) * sizeof(char*));
    for(unsigned j = i; j < i + 5; ++j) {
      argv[j] = (char*) malloc(sizeof(char) * maxoptlen);
      argv[j][0] = '\0';
    }
    argv[i + 5] = NULL;
  }

  strncpy(argv[i], opt, maxoptlen - 1);
  argv[i][maxoptlen - 1] = '\0'; // ensure NUL-termination even on overflow
}

namespace options {

/** Set a given Options* as "current" just for a particular scope. */
class OptionsGuard {
  CVC4_THREADLOCAL_TYPE(Options*)* d_field;
  Options* d_old;
public:
  OptionsGuard(CVC4_THREADLOCAL_TYPE(Options*)* field, Options* opts) :
    d_field(field),
    d_old(*field) {
    *field = opts;
  }
  ~OptionsGuard() {
    *d_field = d_old;
  }
};/* class OptionsGuard */

}/* CVC4::options namespace */

/**
 * Parse argc/argv and put the result into a CVC4::Options.
 * The return value is what's left of the command line (that is, the
 * non-option arguments).
 */
std::vector<std::string> Options::parseOptions(int argc, char* main_argv[]) throw(OptionException) {
  options::OptionsGuard guard(&s_current, this);

  const char *progName = main_argv[0];
  SmtEngine* const smt = NULL;

  Debug("options") << "main_argv == " << main_argv << std::endl;

  // Reset getopt(), in the case of multiple calls to parseOptions().
  // This can be = 1 in newer GNU getopt, but older (< 2007) require = 0.
  optind = 0;
#if HAVE_DECL_OPTRESET
  optreset = 1; // on BSD getopt() (e.g. Mac OS), might need this
#endif /* HAVE_DECL_OPTRESET */

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL) {
    progName = x + 1;
  }
  d_holder->binary_name = std::string(progName);

  int extra_argc = 1;
  char **extra_argv = (char**) malloc(2 * sizeof(char*));
  extra_argv[0] = NULL;
  extra_argv[1] = NULL;

  int extra_optind = 0, main_optind = 0;
  int old_optind;
  int *optind_ref = &main_optind;

  char** argv = main_argv;

  std::vector<std::string> nonOptions;

  for(;;) {
    int c = -1;
    optopt = 0;
    std::string option, optionarg;
    Debug("preemptGetopt") << "top of loop, extra_optind == " << extra_optind << ", extra_argc == " << extra_argc << std::endl;
    if((extra_optind == 0 ? 1 : extra_optind) < extra_argc) {
#if HAVE_DECL_OPTRESET
      if(optind_ref != &extra_optind) {
        optreset = 1; // on BSD getopt() (e.g. Mac OS), might need this
      }
#endif /* HAVE_DECL_OPTRESET */
      old_optind = optind = extra_optind;
      optind_ref = &extra_optind;
      argv = extra_argv;
      Debug("preemptGetopt") << "in preempt code, next arg is " << extra_argv[optind == 0 ? 1 : optind] << std::endl;
      if(extra_argv[extra_optind == 0 ? 1 : extra_optind][0] != '-') {
        InternalError("preempted args cannot give non-options command-line args (found `%s')", extra_argv[extra_optind == 0 ? 1 : extra_optind]);
      }
      c = getopt_long(extra_argc, extra_argv,
                      "+:${all_modules_short_options}",
                      cmdlineOptions, NULL);
      Debug("preemptGetopt") << "in preempt code, c == " << c << " (`" << char(c) << "') optind == " << optind << std::endl;
      if(optopt == 0 ||
         ( optopt >= ${long_option_value_begin} && optopt <= ${long_option_value_end} )) {
        // long option
        option = argv[old_optind == 0 ? 1 : old_optind];
        optionarg = (optarg == NULL) ? "" : optarg;
      } else {
        // short option
        option = std::string("-") + char(optopt);
        optionarg = (optarg == NULL) ? "" : optarg;
      }
      if(optind >= extra_argc) {
        Debug("preemptGetopt") << "-- no more preempt args" << std::endl;
        unsigned i = 1;
        while(extra_argv[i] != NULL && extra_argv[i][0] != '\0') {
          extra_argv[i][0] = '\0';
          ++i;
        }
        extra_argc = 1;
        extra_optind = 0;
      } else {
        Debug("preemptGetopt") << "-- more preempt args" << std::endl;
        extra_optind = optind;
      }
    }
    if(c == -1) {
#if HAVE_DECL_OPTRESET
      if(optind_ref != &main_optind) {
        optreset = 1; // on BSD getopt() (e.g. Mac OS), might need this
      }
#endif /* HAVE_DECL_OPTRESET */
      old_optind = optind = main_optind;
      optind_ref = &main_optind;
      argv = main_argv;
      if(main_optind < argc && main_argv[main_optind][0] != '-') {
        do {
          if(main_optind != 0) {
            nonOptions.push_back(main_argv[main_optind]);
          }
          ++main_optind;
        } while(main_optind < argc && main_argv[main_optind][0] != '-');
        continue;
      }
      Debug("options") << "[ before, optind == " << optind << " ]" << std::endl;
#if defined(__MINGW32__) || defined(__MINGW64__)
      if(optreset == 1 && optind > 1) {
        // on mingw, optreset will reset the optind, so we have to
        // manually advance argc, argv
        main_argv[optind - 1] = main_argv[0];
        argv = main_argv += optind - 1;
        argc -= optind - 1;
        old_optind = optind = main_optind = 1;
        if(argc > 0) {
          Debug("options") << "looking at : " << argv[0] << std::endl;
        }
        /*c = getopt_long(argc, main_argv,
                        "+:${all_modules_short_options}",
                        cmdlineOptions, NULL);
        Debug("options") << "pre-emptory c is " << c << " (" << char(c) << ")" << std::endl;
        Debug("options") << "optind was reset to " << optind << std::endl;
        optind = main_optind;
        Debug("options") << "I restored optind to " << optind << std::endl;*/
      }
#endif /* __MINGW32__ || __MINGW64__ */
      Debug("options") << "[ argc == " << argc << ", main_argv == " << main_argv << " ]" << std::endl;
      c = getopt_long(argc, main_argv,
                      "+:${all_modules_short_options}",
                      cmdlineOptions, NULL);
      main_optind = optind;
      Debug("options") << "[ got " << int(c) << " (" << char(c) << ") ]" << std::endl;
      Debug("options") << "[ next option will be at pos: " << optind << " ]" << std::endl;
      if(c == -1) {
        Debug("options") << "done with option parsing" << std::endl;
        break;
      }
      option = argv[old_optind == 0 ? 1 : old_optind];
      optionarg = (optarg == NULL) ? "" : optarg;
    }

    Debug("preemptGetopt") << "processing option " << c << " (`" << char(c) << "'), " << option << std::endl;

    switch(c) {
${all_modules_option_handlers}

#line 508 "${template}"

    case ':':
      // This can be a long or short option, and the way to get at the
      // name of it is different.
      throw OptionException(std::string("option `") + option + "' missing its required argument");

    case '?':
    default:
      if( ( optopt == 0 || ( optopt >= ${long_option_value_begin} && optopt <= ${long_option_value_end} ) ) &&
          !strncmp(argv[optind - 1], "--thread", 8) &&
          strlen(argv[optind - 1]) > 8 ) {
        if(! isdigit(argv[optind - 1][8])) {
          throw OptionException(std::string("can't understand option `") + option + "': expected something like --threadN=\"--option1 --option2\", where N is a nonnegative integer");
        }
        std::vector<std::string>& threadArgv = d_holder->threadArgv;
        char *end;
        long tnum = strtol(argv[optind - 1] + 8, &end, 10);
        if(tnum < 0 || (*end != '\0' && *end != '=')) {
          throw OptionException(std::string("can't understand option `") + option + "': expected something like --threadN=\"--option1 --option2\", where N is a nonnegative integer");
        }
        if(threadArgv.size() <= size_t(tnum)) {
          threadArgv.resize(tnum + 1);
        }
        if(threadArgv[tnum] != "") {
          threadArgv[tnum] += " ";
        }
        if(*end == '\0') { // e.g., we have --thread0 "foo"
          if(argc <= optind) {
            throw OptionException(std::string("option `") + option + "' missing its required argument");
          }
          Debug("options") << "thread " << tnum << " gets option " << argv[optind] << std::endl;
          threadArgv[tnum] += argv[(*optind_ref)++];
        } else { // e.g., we have --thread0="foo"
          if(end[1] == '\0') {
            throw OptionException(std::string("option `") + option + "' missing its required argument");
          }
          Debug("options") << "thread " << tnum << " gets option " << (end + 1) << std::endl;
          threadArgv[tnum] += end + 1;
        }
        Debug("options") << "thread " << tnum << " now has " << threadArgv[tnum] << std::endl;
        break;
      }

      throw OptionException(std::string("can't understand option `") + option + "'");
    }
  }

  Debug("options") << "returning " << nonOptions.size() << " non-option arguments." << std::endl;

  return nonOptions;
}

std::vector<std::string> Options::suggestCommandLineOptions(const std::string& optionName) throw() {
  std::vector<std::string> suggestions;

  const char* opt;
  for(size_t i = 0; (opt = cmdlineOptions[i].name) != NULL; ++i) {
    if(std::strstr(opt, optionName.c_str()) != NULL) {
      suggestions.push_back(opt);
    }
  }

  return suggestions;
}

static const char* smtOptions[] = {
  ${all_modules_smt_options},
#line 576 "${template}"
  NULL
};/* smtOptions[] */

std::vector<std::string> Options::suggestSmtOptions(const std::string& optionName) throw() {
  std::vector<std::string> suggestions;

  const char* opt;
  for(size_t i = 0; (opt = smtOptions[i]) != NULL; ++i) {
    if(std::strstr(opt, optionName.c_str()) != NULL) {
      suggestions.push_back(opt);
    }
  }

  return suggestions;
}

SExpr Options::getOptions() const throw() {
  std::vector<SExpr> opts;

  ${all_modules_get_options}

#line 598 "${template}"

  return SExpr(opts);
}

#undef USE_EARLY_TYPE_CHECKING_BY_DEFAULT
#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}/* CVC4 namespace */
