/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "options/option_exception.h"
#include "util/didyoumean.h"

#include <cstring>
#include <iostream>
#include <limits>

namespace cvc5::main {

using namespace cvc5::internal;

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
// clang-format on

void printUsage(const std::string& binary, std::ostream& os)
{
  os << "usage: " << binary << " [options] [input-file]" << std::endl
     << std::endl
     << "Without an input file, or with `-', cvc5 reads from standard "
        "input."
     << std::endl
     << std::endl
     << "cvc5 options:" << std::endl
     << commonOptionsDescription << std::endl
     << std::endl
     << additionalOptionsDescription << std::endl
     << optionsFootnote << std::endl;
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

void parseInternal(cvc5::Solver& solver,
                   int argc,
                   char* argv[],
                   std::vector<std::string>& nonoptions)
{
  Assert(argv != nullptr);
  if (TraceIsOn("options"))
  {
    Trace("options") << "starting a new parseInternal with " << argc
                     << " arguments" << std::endl;
    for (int i = 0; i < argc; ++i)
    {
      Assert(argv[i] != nullptr);
      Trace("options") << "  argv[" << i << "] = " << argv[i] << std::endl;
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
      Trace("options") << "enqueueing " << argv[main_optind]
                       << " as a non-option." << std::endl;
      nonoptions.push_back(argv[main_optind]);
      ++main_optind;
      continue;
    }

    Trace("options") << "[ before, main_optind == " << main_optind << " ]"
                     << std::endl;
    Trace("options") << "[ before, optind == " << optind << " ]" << std::endl;
    Trace("options") << "[ argc == " << argc << ", argv == " << argv << " ]"
                     << std::endl;
    // clang-format off
    int c = getopt_long(argc, argv,
                        "+:${cmdoptions_short}$",
                        cmdlineOptions, nullptr);
    // clang-format on

    main_optind = optind;

    Trace("options") << "[ got " << int(c) << " (" << char(c) << ") ]"
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
      if (TraceIsOn("options"))
      {
        Trace("options") << "done with option parsing" << std::endl;
        for (int index = optind; index < argc; ++index)
        {
          Trace("options") << "remaining " << argv[index] << std::endl;
        }
      }
      break;
    }

    std::string option = argv[old_optind == 0 ? 1 : old_optind];
    std::string optionarg = (optarg == nullptr) ? "" : optarg;

    Trace("preemptGetopt") << "processing option " << c << " (`" << char(c)
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

  Trace("options") << "got " << nonoptions.size() << " non-option arguments."
                   << std::endl;
}

/**
 * Parse argc/argv and put the result into a cvc5::internal::Options.
 * The return value is what's left of the command line (that is, the
 * non-option arguments).
 *
 * Throws OptionException on failures.
 */
std::vector<std::string> parse(cvc5::Solver& solver,
                               int argc,
                               char* argv[],
                               std::string& binaryName)
{
  Assert(argv != nullptr);

  const char* progName = argv[0];

  // To debug options parsing, you may prefer to simply uncomment this
  // and recompile. Debug flags have not been parsed yet so these have
  // not been set.
  // TraceChannel.on("options");

  Trace("options") << "argv == " << argv << std::endl;

  // Find the base name of the program.
  const char* x = strrchr(progName, '/');
  if (x != nullptr)
  {
    progName = x + 1;
  }
  binaryName = std::string(progName);

  std::vector<std::string> nonoptions;
  parseInternal(solver, argc, argv, nonoptions);
  if (TraceIsOn("options"))
  {
    for (const auto& no : nonoptions)
    {
      Trace("options") << "nonoptions " << no << std::endl;
    }
  }

  return nonoptions;
}

}  // namespace cvc5::main
