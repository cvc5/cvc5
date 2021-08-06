/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "options/options_public.h"

#if !defined(_BSD_SOURCE) && defined(__MINGW32__) && !defined(__MINGW64__)
// force use of optreset; mingw32 croaks on argv-switching otherwise
#include "base/cvc5config.h"
#define _BSD_SOURCE
#undef HAVE_DECL_OPTRESET
#define HAVE_DECL_OPTRESET 1
#define CVC5_IS_NOT_REALLY_BSD
#endif /* !_BSD_SOURCE && __MINGW32__ && !__MINGW64__ */

#ifdef __MINGW64__
extern int optreset;
#endif /* __MINGW64__ */

#include <getopt.h>

// clean up
#ifdef CVC5_IS_NOT_REALLY_BSD
#  undef _BSD_SOURCE
#endif /* CVC5_IS_NOT_REALLY_BSD */

#include "base/check.h"
#include "base/output.h"
#include "options/didyoumean.h"
#include "options/options_handler.h"
#include "options/options_listener.h"
#include "options/options.h"
#include "options/uf_options.h"
${headers_module}$
${headers_handler}$

#include <cstring>
#include <iostream>
#include <limits>

namespace cvc5::options {

bool getUfHo(const Options& opts) { return opts.uf.ufHo; }

// clang-format off
static const std::string mostCommonOptionsDescription =
    "\
Most commonly-used cvc5 options:\n"
${help_common}$
    ;

static const std::string optionsDescription =
    mostCommonOptionsDescription + "\n\nAdditional cvc5 options:\n"
${help_others}$;

static const std::string optionsFootnote = "\n\
[*] Each of these options has a --no-OPTIONNAME variant, which reverses the\n\
    sense of the option.\n\
";

static const std::string languageDescription =
    "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto                           attempt to automatically determine language\n\
  cvc | presentation | pl        CVC presentation language\n\
  smt | smtlib | smt2 |\n\
  smt2.6 | smtlib2.6             SMT-LIB format 2.6 with support for the strings standard\n\
  tptp                           TPTP format (cnf, fof and tff)\n\
  sygus | sygus2                 SyGuS version 2.0\n\
\n\
Languages currently supported as arguments to the --output-lang option:\n\
  auto                           match output language to input language\n\
  cvc | presentation | pl        CVC presentation language\n\
  smt | smtlib | smt2 |\n\
  smt2.6 | smtlib2.6             SMT-LIB format 2.6 with support for the strings standard\n\
  tptp                           TPTP format\n\
  ast                            internal format (simple syntax trees)\n\
";
// clang-format on

const std::string& getDescription()
{
  return optionsDescription;
}

void printUsage(const std::string& msg, std::ostream& os) {
  os << msg << optionsDescription << std::endl
      << optionsFootnote << std::endl << std::flush;
}

void printShortUsage(const std::string& msg, std::ostream& os) {
  os << msg << mostCommonOptionsDescription << std::endl
      << optionsFootnote << std::endl
      << "For full usage, please use --help."
      << std::endl << std::endl << std::flush;
}

void printLanguageHelp(std::ostream& os) {
  os << languageDescription << std::flush;
}

/** Set a given Options* as "current" just for a particular scope. */
class OptionsGuard {
  Options** d_field;
  Options* d_old;
public:
  OptionsGuard(Options** field, Options* opts) :
    d_field(field),
    d_old(*field) {
    *field = opts;
  }
  ~OptionsGuard() {
    *d_field = d_old;
  }
};/* class OptionsGuard */

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
 * add it to the getopt_long() call in parse().
 */
// clang-format off
static struct option cmdlineOptions[] = {
  ${cmdline_options}$
  {nullptr, no_argument, nullptr, '\0'}};
// clang-format on

std::string suggestCommandLineOptions(const std::string& optionName)
{
  DidYouMean didYouMean;

  const char* opt;
  for(size_t i = 0; (opt = cmdlineOptions[i].name) != nullptr; ++i) {
    didYouMean.addWord(std::string("--") + cmdlineOptions[i].name);
  }

  return didYouMean.getMatchAsString(optionName.substr(0, optionName.find('=')));
}

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
  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg);
};/* struct OptionHandler<> */

/** Variant for integral C++ types */
template <class T>
struct OptionHandler<T, true, true> {
  static bool stringToInt(T& t, const std::string& str) {
    std::istringstream ss(str);
    ss >> t;
    char tmp;
    return !(ss.fail() || ss.get(tmp));
  }

  static bool containsMinus(const std::string& str) {
    return str.find('-') != std::string::npos;
  }

  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg) {
    try {
      T i;
      bool success = stringToInt(i, optionarg);

      if(!success){
        throw OptionException(flag + ": failed to parse "+ optionarg +
                              " as an integer of the appropriate type.");
      }

      // Depending in the platform unsigned numbers with '-' signs may parse.
      // Reject these by looking for any minus if it is not signed.
      if( (! std::numeric_limits<T>::is_signed) && containsMinus(optionarg) ) {
        // unsigned type but user gave negative argument
        throw OptionException(flag + " requires a nonnegative argument");
      } else if(i < std::numeric_limits<T>::min()) {
        // negative overflow for type
        std::stringstream ss;
        ss << flag << " requires an argument >= "
           << std::numeric_limits<T>::min();
        throw OptionException(ss.str());
      } else if(i > std::numeric_limits<T>::max()) {
        // positive overflow for type
        std::stringstream ss;
        ss << flag << " requires an argument <= "
           << std::numeric_limits<T>::max();
        throw OptionException(ss.str());
      }

      return i;

      // if(std::numeric_limits<T>::is_signed) {
      //   return T(i.getLong());
      // } else {
      //   return T(i.getUnsignedLong());
      // }
    } catch(std::invalid_argument&) {
      // user gave something other than an integer
      throw OptionException(flag + " requires an integer argument");
    }
  }
};/* struct OptionHandler<T, true, true> */

/** Variant for numeric but non-integral C++ types */
template <class T>
struct OptionHandler<T, true, false> {
  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg) {
    std::stringstream inss(optionarg);
    long double r;
    inss >> r;
    if(! inss.eof()) {
      // we didn't consume the whole string (junk at end)
      throw OptionException(flag + " requires a numeric argument");
    }

    if(! std::numeric_limits<T>::is_signed && r < 0.0) {
      // unsigned type but user gave negative value
      throw OptionException(flag + " requires a nonnegative argument");
    } else if(r < -std::numeric_limits<T>::max()) {
      // negative overflow for type
      std::stringstream ss;
      ss << flag << " requires an argument >= "
         << -std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    } else if(r > std::numeric_limits<T>::max()) {
      // positive overflow for type
      std::stringstream ss;
      ss << flag << " requires an argument <= "
         << std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    }

    return T(r);
  }
};/* struct OptionHandler<T, true, false> */

/** Variant for non-numeric C++ types */
template <class T>
struct OptionHandler<T, false, false> {
  static T handle(const std::string& option, const std::string& flag, const std::string& optionarg) {
    T::unsupported_handleOption_call___please_write_me;
    // The above line causes a compiler error if this version of the template
    // is ever instantiated (meaning that a specialization is missing).  So
    // don't worry about the segfault in the next line, the "return" is only
    // there to keep the compiler from giving additional, distracting errors
    // and warnings.
    return *(T*)0;
  }
};/* struct OptionHandler<T, false, false> */

/** Specialization for ManagedErr */
template <>
struct OptionHandler<ManagedErr, false, false>
{
  static ManagedErr handle(const std::string& option,
                           const std::string& flag,
                           const std::string& optionarg)
  {
    ManagedErr res;
    res.open(optionarg);
    return res;
  }
};
/** Specialization for ManagedIn */
template <>
struct OptionHandler<ManagedIn, false, false>
{
  static ManagedIn handle(const std::string& option,
                          const std::string& flag,
                          const std::string& optionarg)
  {
    ManagedIn res;
    res.open(optionarg);
    return res;
  }
};
/** Specialization for ManagedOut */
template <>
struct OptionHandler<ManagedOut, false, false>
{
  static ManagedOut handle(const std::string& option,
                           const std::string& flag,
                           const std::string& optionarg)
  {
    ManagedOut res;
    res.open(optionarg);
    return res;
  }
};

/** Handle an option of type T in the default way. */
template <class T>
T handleOption(const std::string& option, const std::string& flag, const std::string& optionarg) {
  return OptionHandler<T, std::numeric_limits<T>::is_specialized, std::numeric_limits<T>::is_integer>::handle(option, flag, optionarg);
}

/** Handle an option of type std::string in the default way. */
template <>
std::string handleOption<std::string>(const std::string& option, const std::string& flag, const std::string& optionarg) {
  return optionarg;
}

// clang-format off
${assigns}$
// clang-format off

void parseInternal(Options& opts, int argc,
                                    char* argv[],
                                    std::vector<std::string>& nonoptions)
{
  Assert(argv != nullptr);
  if(Debug.isOn("options")) {
    Debug("options") << "starting a new parseInternal with "
                     << argc << " arguments" << std::endl;
    for( int i = 0; i < argc ; i++ ){
      Assert(argv[i] != NULL);
      Debug("options") << "  argv[" << i << "] = " << argv[i] << std::endl;
    }
  }

  // Reset getopt(), in the case of multiple calls to parse().
  // This can be = 1 in newer GNU getopt, but older (< 2007) require = 0.
  optind = 0;
#if HAVE_DECL_OPTRESET
  optreset = 1; // on BSD getopt() (e.g. Mac OS), might need this
#endif /* HAVE_DECL_OPTRESET */

  // We must parse the binary name, which is manually ignored below. Setting
  // this to 1 leads to incorrect behavior on some platforms.
  int main_optind = 0;
  int old_optind;


  while(true) { // Repeat Forever

    optopt = 0;
    std::string option, optionarg;

    optind = main_optind;
    old_optind = main_optind;

    // If we encounter an element that is not at zero and does not start
    // with a "-", this is a non-option. We consume this element as a
    // non-option.
    if (main_optind > 0 && main_optind < argc &&
        argv[main_optind][0] != '-') {
      Debug("options") << "enqueueing " << argv[main_optind]
                       << " as a non-option." << std::endl;
      nonoptions.push_back(argv[main_optind]);
      ++main_optind;
      continue;
    }


    Debug("options") << "[ before, main_optind == " << main_optind << " ]"
                     << std::endl;
    Debug("options") << "[ before, optind == " << optind << " ]" << std::endl;
    Debug("options") << "[ argc == " << argc << ", argv == " << argv << " ]"
                     << std::endl;
    // clang-format off
    int c = getopt_long(argc, argv,
                        "+:${options_short}$",
                        cmdlineOptions, NULL);
    // clang-format on

    main_optind = optind;

    Debug("options") << "[ got " << int(c) << " (" << char(c) << ") ]"
                     << "[ next option will be at pos: " << optind << " ]"
                     << std::endl;

    // The initial getopt_long call should always determine that argv[0]
    // is not an option and returns -1. We always manually advance beyond
    // this element.
    if ( old_optind == 0  && c == -1 ) {
      Assert(main_optind > 0);
      continue;
    }

    if ( c == -1 ) {
      if(Debug.isOn("options")) {
        Debug("options") << "done with option parsing" << std::endl;
        for(int index = optind; index < argc; ++index) {
          Debug("options") << "remaining " << argv[index] << std::endl;
        }
      }
      break;
    }

    option = argv[old_optind == 0 ? 1 : old_optind];
    optionarg = (optarg == NULL) ? "" : optarg;

    Debug("preemptGetopt") << "processing option " << c
                           << " (`" << char(c) << "'), " << option << std::endl;

    // clang-format off
    switch(c)
    {
${options_handler}$

      case ':' :
      // This can be a long or short option, and the way to get at the
      // name of it is different.
      throw OptionException(std::string("option `") + option
                            + "' missing its required argument");

      case '?':
      default:
        throw OptionException(std::string("can't understand option `") + option
                              + "'" + suggestCommandLineOptions(option));
    }
  }
  // clang-format on

  Debug("options") << "got " << nonoptions.size()
                   << " non-option arguments." << std::endl;
}

/**
 * Parse argc/argv and put the result into a cvc5::Options.
 * The return value is what's left of the command line (that is, the
 * non-option arguments).
 *
 * Throws OptionException on failures.
 */
std::vector<std::string> parse(
    Options & opts, int argc, char* argv[], std::string& binaryName)
{
  Assert(argv != nullptr);

  Options* cur = &Options::current();
  OptionsGuard guard(&cur, &opts);

  const char *progName = argv[0];

  // To debug options parsing, you may prefer to simply uncomment this
  // and recompile. Debug flags have not been parsed yet so these have
  // not been set.
  //DebugChannel.on("options");

  Debug("options") << "options::parse == " << &opts << std::endl;
  Debug("options") << "argv == " << argv << std::endl;

  // Find the base name of the program.
  const char *x = strrchr(progName, '/');
  if(x != nullptr) {
    progName = x + 1;
  }
  binaryName = std::string(progName);

  std::vector<std::string> nonoptions;
  parseInternal(opts, argc, argv, nonoptions);
  if (Debug.isOn("options")){
    for(std::vector<std::string>::const_iterator i = nonoptions.begin(),
          iend = nonoptions.end(); i != iend; ++i){
      Debug("options") << "nonoptions " << *i << std::endl;
    }
  }

  return nonoptions;
}

std::string get(const Options& options, const std::string& name)
{
  Trace("options") << "Options::getOption(" << name << ")" << std::endl;
  ${getoption_handlers}$

  throw UnrecognizedOptionException(name);
}

void setInternal(Options& opts, const std::string& name,
                                const std::string& optionarg)
                                {
${setoption_handlers}$
  throw UnrecognizedOptionException(name);
}

void set(Options& opts, const std::string& name, const std::string& optionarg)
{

  Trace("options") << "setOption(" << name << ", " << optionarg << ")"
                   << std::endl;
  // first update this object
  setInternal(opts, name, optionarg);
}

std::vector<std::vector<std::string> > getAll(const Options& opts)
{
  std::vector<std::vector<std::string>> res;

${options_getall}$

  return res;
}

std::vector<std::string> getNames()
{
  return {
${options_all_names}$
  };
}

}  // namespace cvc5::options
