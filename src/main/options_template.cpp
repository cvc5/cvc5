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
 * Options utilities used in the driver.
 */

#include "main/options.h"

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
#include "options/option_exception.h"

#include <cstring>
#include <iostream>
#include <limits>

namespace cvc5::main {

// clang-format off
static const std::string commonOptionsDescription =
R"FOOBAR(Most commonly-used cvc5 options:
${help_common}$
)FOOBAR";

static const std::string additionalOptionsDescription =
R"FOOBAR(Additional cvc5 options:
${help_others}$
)FOOBAR";

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

void printUsage(const std::string& msg, std::ostream& os)
{
  os << msg << "\n"
     << commonOptionsDescription << "\n\n"
     << additionalOptionsDescription << std::endl
     << optionsFootnote << std::endl;
}

void printShortUsage(const std::string& msg, std::ostream& os)
{
  os << msg << "\n"
     << commonOptionsDescription << std::endl
     << optionsFootnote << std::endl
     << "For full usage, please use --help." << std::endl
     << std::endl;
}

void printLanguageHelp(std::ostream& os)
{
  os << languageDescription << std::flush;
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
 *    array if the option is present; or nullptr, in which case
 *    getopt_long() returns the 4th entry
 * 4. the return value for getopt_long() when this long option (or the
 *    value to set the 3rd entry to; see #3)
 */
static struct option cmdlineOptions[] = {
// clang-format off
  ${cmdoptions_long}$
// clang-format on
  {nullptr, no_argument, nullptr, '\0'}
};

std::string suggestCommandLineOptions(const std::string& optionName)
{
  DidYouMean didYouMean;

  const char* opt;
  for (size_t i = 0; (opt = cmdlineOptions[i].name) != nullptr; ++i)
  {
    didYouMean.addWord(std::string("--") + cmdlineOptions[i].name);
  }

  return didYouMean.getMatchAsString(
      optionName.substr(0, optionName.find('=')));
}

void parseInternal(api::Solver& solver,
                   int argc,
                   char* argv[],
                   std::vector<std::string>& nonoptions)
{
  Assert(argv != nullptr);
  if (Debug.isOn("options"))
  {
    Debug("options") << "starting a new parseInternal with " << argc
                     << " arguments" << std::endl;
    for (int i = 0; i < argc; ++i)
    {
      Assert(argv[i] != nullptr);
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

  while (true)
  {  // Repeat Forever

    optopt = 0;

    optind = main_optind;
    old_optind = main_optind;

    // If we encounter an element that is not at zero and does not start
    // with a "-", this is a non-option. We consume this element as a
    // non-option.
    if (main_optind > 0 && main_optind < argc && argv[main_optind][0] != '-')
    {
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
                        "+:${cmdoptions_short}$",
                        cmdlineOptions, nullptr);
    // clang-format on

    main_optind = optind;

    Debug("options") << "[ got " << int(c) << " (" << char(c) << ") ]"
                     << "[ next option will be at pos: " << optind << " ]"
                     << std::endl;

    // The initial getopt_long call should always determine that argv[0]
    // is not an option and returns -1. We always manually advance beyond
    // this element.
    if (old_optind == 0 && c == -1)
    {
      Assert(main_optind > 0);
      continue;
    }

    if (c == -1)
    {
      if (Debug.isOn("options"))
      {
        Debug("options") << "done with option parsing" << std::endl;
        for (int index = optind; index < argc; ++index)
        {
          Debug("options") << "remaining " << argv[index] << std::endl;
        }
      }
      break;
    }

    std::string option = argv[old_optind == 0 ? 1 : old_optind];
    std::string optionarg = (optarg == nullptr) ? "" : optarg;

    Debug("preemptGetopt") << "processing option " << c << " (`" << char(c)
                           << "'), " << option << std::endl;

    switch (c)
    {
// clang-format off
    ${parseinternal_impl}$
// clang-format on

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

  Debug("options") << "got " << nonoptions.size() << " non-option arguments."
                   << std::endl;
}

/**
 * Parse argc/argv and put the result into a cvc5::Options.
 * The return value is what's left of the command line (that is, the
 * non-option arguments).
 *
 * Throws OptionException on failures.
 */
std::vector<std::string> parse(api::Solver& solver,
                               int argc,
                               char* argv[],
                               std::string& binaryName)
{
  Assert(argv != nullptr);

  const char* progName = argv[0];

  // To debug options parsing, you may prefer to simply uncomment this
  // and recompile. Debug flags have not been parsed yet so these have
  // not been set.
  // DebugChannel.on("options");

  Debug("options") << "argv == " << argv << std::endl;

  // Find the base name of the program.
  const char* x = strrchr(progName, '/');
  if (x != nullptr)
  {
    progName = x + 1;
  }
  binaryName = std::string(progName);

  std::vector<std::string> nonoptions;
  parseInternal(solver, argc, argv, nonoptions);
  if (Debug.isOn("options"))
  {
    for (const auto& no : nonoptions)
    {
      Debug("options") << "nonoptions " << no << std::endl;
    }
  }

  return nonoptions;
}

}  // namespace cvc5::options
