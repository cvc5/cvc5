/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Interface for custom handlers and predicates options.
 */

#include "options/options_handler.h"

#include <cerrno>
#include <iostream>
#include <ostream>
#include <regex>
#include <string>

#include "base/check.h"
#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/cvc5config.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "lib/strtok_r.h"
#include "options/base_options.h"
#include "options/bv_options.h"
#include "options/decision_options.h"
#include "options/io_utils.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "util/didyoumean.h"

namespace cvc5::internal {
namespace options {

// helper functions
namespace {

void printTags(const std::vector<std::string>& tags)
{
  std::cout << "available tags:" << std::endl;
  for (const auto& t : tags)
  {
    std::cout << "  " << t << std::endl;
  }
  std::cout << std::endl;
}

std::string suggestTags(const std::vector<std::string>& validTags,
                        std::string inputTag,
                        const std::vector<std::string>& additionalTags)
{
  DidYouMean didYouMean;
  didYouMean.addWords(validTags);
  didYouMean.addWords(additionalTags);
  return didYouMean.getMatchAsString(inputTag);
}

/**
 * Select all tags from validTags that match the given (globbing) pattern.
 * The pattern may contain `*` as wildcards. These are internally converted to
 * `.*` and matched using std::regex. If no wildcards are present, regular
 * string comparisons are used.
 */
std::vector<std::string> selectTags(const std::vector<std::string>& validTags, std::string pattern)
{
  bool isRegex = false;
  size_t pos = 0;
  while ((pos = pattern.find('*', pos)) != std::string::npos)
  {
    pattern.replace(pos, 1, ".*");
    pos += 2;
    isRegex = true;
  }
  std::vector<std::string> results;
  if (isRegex)
  {
    std::regex re(pattern);
    std::copy_if(validTags.begin(), validTags.end(), std::back_inserter(results),
      [&re](const auto& tag){ return std::regex_match(tag, re); }
    );
  }
  else
  {
    if (std::find(validTags.begin(), validTags.end(), pattern) != validTags.end())
    {
      results.emplace_back(pattern);
    }
  }
  return results;
}

}  // namespace

OptionsHandler::OptionsHandler(Options* options) : d_options(options) { }

void OptionsHandler::setErrStream(const std::string& flag, const ManagedErr& me)
{
  Warning.setStream(me);
  TraceChannel.setStream(me);
}

Language OptionsHandler::stringToLanguage(const std::string& flag,
                                          const std::string& optarg)
{
  if (optarg == "help")
  {
    *d_options->base.out << R"FOOBAR(
Languages currently supported as arguments to the -L / --lang option:
  auto                           attempt to automatically determine language
  smt | smtlib | smt2 |
  smt2.6 | smtlib2.6             SMT-LIB format 2.6 with support for the strings standard
  sygus | sygus2                 SyGuS version 2.0

Languages currently supported as arguments to the --output-lang option:
  auto                           match output language to input language
  smt | smtlib | smt2 |
  smt2.6 | smtlib2.6             SMT-LIB format 2.6 with support for the strings standard
  ast                            internal format (simple syntax trees)
)FOOBAR" << std::endl;
    throw OptionException("help is not a valid language");
  }

  try
  {
    return language::toLanguage(optarg);
  }
  catch (OptionException& oe)
  {
    throw OptionException("Error in " + flag + ": " + oe.getMessage()
                          + "\nTry --lang help");
  }

  Unreachable();
}

void OptionsHandler::setInputLanguage(const std::string& flag, Language lang)
{
  if (lang == Language::LANG_AST)
  {
    throw OptionException("Language LANG_AST is not allowed for " + flag);
  }
  if (!d_options->printer.outputLanguageWasSetByUser)
  {
    d_options->writePrinter().outputLanguage = lang;
    ioutils::setDefaultOutputLanguage(lang);
  }
}

void OptionsHandler::setVerbosity(const std::string& flag, int value)
{
  if(Configuration::isMuzzledBuild()) {
    TraceChannel.setStream(&cvc5::internal::null_os);
    WarningChannel.setStream(&cvc5::internal::null_os);
  } else {
    if(value < 0) {
      WarningChannel.setStream(&cvc5::internal::null_os);
    } else {
      WarningChannel.setStream(&std::cerr);
    }
  }
}

void OptionsHandler::decreaseVerbosity(const std::string& flag, bool value)
{
  d_options->writeBase().verbosity -= 1;
  setVerbosity(flag, d_options->base.verbosity);
}

void OptionsHandler::increaseVerbosity(const std::string& flag, bool value)
{
  d_options->writeBase().verbosity += 1;
  setVerbosity(flag, d_options->base.verbosity);
}

void OptionsHandler::setStats(const std::string& flag, bool value)
{
#ifndef CVC5_STATISTICS_ON
  if (value)
  {
    std::stringstream ss;
    ss << "option `" << flag
       << "' requires a statistics-enabled build of cvc5; this binary was not "
          "built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC5_STATISTICS_ON */
  if (!value)
  {
    d_options->writeBase().statisticsAll = false;
    d_options->writeBase().statisticsEveryQuery = false;
    d_options->writeBase().statisticsInternal = false;
  }
}

void OptionsHandler::setStatsDetail(const std::string& flag, bool value)
{
#ifndef CVC5_STATISTICS_ON
  if (value)
  {
    std::stringstream ss;
    ss << "option `" << flag
       << "' requires a statistics-enabled build of cvc5; this binary was not "
          "built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC5_STATISTICS_ON */
  if (value)
  {
    d_options->writeBase().statistics = true;
  }
}

void OptionsHandler::enableTraceTag(const std::string& flag,
                                    const std::string& optarg)
{
  if(!Configuration::isTracingBuild())
  {
    throw OptionException("trace tags not available in non-tracing builds");
  }
  auto tags = selectTags(Configuration::getTraceTags(), optarg);
  if (tags.empty())
  {
    if (optarg == "help")
    {
      d_options->writeDriver().showTraceTags = true;
      showTraceTags("", true);
      return;
    }

    throw OptionException(
        std::string("no trace tag matching ") + optarg + std::string(" was found.")
        + suggestTags(Configuration::getTraceTags(), optarg, {}));
  }
  for (const auto& tag: tags)
  {
    TraceChannel.on(tag);
  }
}

void OptionsHandler::enableOutputTag(const std::string& flag,
                                     OutputTag optarg)
{
  size_t tagid = static_cast<size_t>(optarg);
  Assert(d_options->base.outputTagHolder.size() > tagid)
      << "Output tag is larger than the bitset that holds it.";
  d_options->writeBase().outputTagHolder.set(tagid);
}

void OptionsHandler::setResourceWeight(const std::string& flag,
                                       const std::string& optarg)
{
  d_options->writeBase().resourceWeightHolder.emplace_back(optarg);
}

void OptionsHandler::checkBvSatSolver(const std::string& flag, SatSolverMode m)
{
  if (m == SatSolverMode::CRYPTOMINISAT
      && !Configuration::isBuiltWithCryptominisat())
  {
    std::stringstream ss;
    ss << "option `" << flag
       << "' requires a CryptoMiniSat build of cvc5; this binary was not built "
          "with CryptoMiniSat support";
    throw OptionException(ss.str());
  }

  if (m == SatSolverMode::KISSAT && !Configuration::isBuiltWithKissat())
  {
    std::stringstream ss;
    ss << "option `" << flag
       << "' requires a Kissat build of cvc5; this binary was not built with "
          "Kissat support";
    throw OptionException(ss.str());
  }

  if (d_options->bv.bvSolver != options::BVSolver::BITBLAST
      && (m == SatSolverMode::CRYPTOMINISAT || m == SatSolverMode::CADICAL
          || m == SatSolverMode::KISSAT))
  {
    if (d_options->bv.bitblastMode == options::BitblastMode::LAZY
        && d_options->bv.bitblastModeWasSetByUser)
    {
      std::string sat_solver;
      if (m == options::SatSolverMode::CADICAL)
      {
        sat_solver = "CaDiCaL";
      }
      else if (m == options::SatSolverMode::KISSAT)
      {
        sat_solver = "Kissat";
      }
      else
      {
        Assert(m == options::SatSolverMode::CRYPTOMINISAT);
        sat_solver = "CryptoMiniSat";
      }
      throw OptionException(sat_solver
                            + " does not support lazy bit-blasting.\n"
                            + "Try --bv-sat-solver=minisat");
    }
    if (!d_options->bv.bitvectorToBoolWasSetByUser)
    {
      d_options->writeBv().bitvectorToBool = true;
    }
  }
}

static void print_config(const char* str, std::string config)
{
  std::string s(str);
  unsigned sz = 14;
  if (s.size() < sz) s.resize(sz, ' ');
  std::cout << s << ": " << config << std::endl;
}

static void print_config_cond(const char* str, bool cond = false)
{
  print_config(str, cond ? "yes" : "no");
}

void OptionsHandler::showConfiguration(const std::string& flag, bool value)
{
  if (!value) return;
  std::cout << Configuration::about() << std::endl;

  print_config("version", Configuration::getVersionString());
  if (Configuration::isGitBuild())
  {
    print_config("scm", Configuration::getGitInfo());
  }
  else
  {
    print_config_cond("scm", false);
  }

  std::cout << std::endl;

  std::stringstream ss;
  ss << Configuration::getVersionString();
  print_config("library", ss.str());

  std::cout << std::endl;

  print_config_cond("debug code", Configuration::isDebugBuild());
  print_config_cond("statistics", configuration::isStatisticsBuild());
  print_config_cond("tracing", Configuration::isTracingBuild());
  print_config_cond("muzzled", Configuration::isMuzzledBuild());
  print_config_cond("assertions", Configuration::isAssertionBuild());
  print_config_cond("coverage", Configuration::isCoverageBuild());
  print_config_cond("profiling", Configuration::isProfilingBuild());
  print_config_cond("asan", Configuration::isAsanBuild());
  print_config_cond("ubsan", Configuration::isUbsanBuild());
  print_config_cond("tsan", Configuration::isTsanBuild());
  print_config_cond("competition", Configuration::isCompetitionBuild());

  std::cout << std::endl;

  print_config_cond("cln", Configuration::isBuiltWithCln());
  print_config_cond("glpk", Configuration::isBuiltWithGlpk());
  print_config_cond("cryptominisat", Configuration::isBuiltWithCryptominisat());
  print_config_cond("gmp", Configuration::isBuiltWithGmp());
  print_config_cond("kissat", Configuration::isBuiltWithKissat());
  print_config_cond("poly", Configuration::isBuiltWithPoly());
  print_config_cond("cocoa", Configuration::isBuiltWithCoCoA());
  print_config_cond("editline", Configuration::isBuiltWithEditline());
}

void OptionsHandler::showCopyright(const std::string& flag, bool value)
{
  if (!value) return;
  std::cout << Configuration::copyright() << std::endl;
}

void OptionsHandler::showVersion(const std::string& flag, bool value)
{
  if (!value) return;
  d_options->base.out << Configuration::about() << std::endl;
}

void OptionsHandler::showTraceTags(const std::string& flag, bool value)
{
  if (!value) return;
  if (!Configuration::isTracingBuild())
  {
    throw OptionException("trace tags not available in non-tracing build");
  }
  printTags(Configuration::getTraceTags());
}

}  // namespace options
}  // namespace cvc5::internal
