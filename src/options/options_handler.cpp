/*********************                                                        */
/*! \file options_handler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface for custom handlers and predicates options.
 **
 ** Interface for custom handlers and predicates options.
 **/

#include "options/options_handler.h"

#include <ostream>
#include <string>
#include <cerrno>

#include "cvc4autoconfig.h"

#include "base/check.h"
#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "lib/strtok_r.h"
#include "options/base_options.h"
#include "options/bv_options.h"
#include "options/decision_options.h"
#include "options/didyoumean.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/smt_options.h"
#include "options/theory_options.h"

namespace CVC4 {
namespace options {

// helper functions
namespace {

void throwLazyBBUnsupported(options::SatSolverMode m)
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
  std::string indent(25, ' ');
  throw OptionException(sat_solver + " does not support lazy bit-blasting.\n"
                        + indent + "Try --bv-sat-solver=minisat");
}

}  // namespace

OptionsHandler::OptionsHandler(Options* options) : d_options(options) { }

void OptionsHandler::notifyBeforeSearch(const std::string& option)
{
  try{
    d_options->d_beforeSearchListeners.notify();
  } catch (ModalException&){
    std::stringstream ss;
    ss << "cannot change option `" << option << "' after final initialization";
    throw ModalException(ss.str());
  }
}


void OptionsHandler::notifyTlimit(const std::string& option) {
  d_options->d_tlimitListeners.notify();
}

void OptionsHandler::notifyTlimitPer(const std::string& option) {
  d_options->d_tlimitPerListeners.notify();
}

void OptionsHandler::notifyRlimit(const std::string& option) {
  d_options->d_rlimitListeners.notify();
}

void OptionsHandler::notifyRlimitPer(const std::string& option) {
  d_options->d_rlimitPerListeners.notify();
}

unsigned long OptionsHandler::limitHandler(std::string option,
                                           std::string optarg)
{
  unsigned long ms;
  std::istringstream convert(optarg);
  if (!(convert >> ms))
  {
    throw OptionException("option `" + option
                          + "` requires a number as an argument");
  }
  return ms;
}

/* options/base_options_handlers.h */
void OptionsHandler::notifyPrintSuccess(std::string option) {
  d_options->d_setPrintSuccessListeners.notify();
}

// theory/quantifiers/options_handlers.h

void OptionsHandler::checkInstWhenMode(std::string option, InstWhenMode mode)
{
  if (mode == InstWhenMode::PRE_FULL)
  {
    throw OptionException(std::string("Mode pre-full for ") + option
                          + " is not supported in this release.");
  }
}

// theory/bv/options_handlers.h
void OptionsHandler::abcEnabledBuild(std::string option, bool value)
{
#ifndef CVC4_USE_ABC
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

void OptionsHandler::abcEnabledBuild(std::string option, std::string value)
{
#ifndef CVC4_USE_ABC
  if(!value.empty()) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

void OptionsHandler::checkBvSatSolver(std::string option, SatSolverMode m)
{
  if (m == SatSolverMode::CRYPTOMINISAT
      && !Configuration::isBuiltWithCryptominisat())
  {
    std::stringstream ss;
    ss << "option `" << option
       << "' requires a CryptoMiniSat build of CVC4; this binary was not built "
          "with CryptoMiniSat support";
    throw OptionException(ss.str());
  }

  if (m == SatSolverMode::CADICAL && !Configuration::isBuiltWithCadical())
  {
    std::stringstream ss;
    ss << "option `" << option
       << "' requires a CaDiCaL build of CVC4; this binary was not built with "
          "CaDiCaL support";
    throw OptionException(ss.str());
  }

  if (m == SatSolverMode::KISSAT && !Configuration::isBuiltWithKissat())
  {
    std::stringstream ss;
    ss << "option `" << option
       << "' requires a Kissat build of CVC4; this binary was not built with "
          "Kissat support";
    throw OptionException(ss.str());
  }

  if (m == SatSolverMode::CRYPTOMINISAT || m == SatSolverMode::CADICAL
      || m == SatSolverMode::KISSAT)
  {
    if (options::bitblastMode() == options::BitblastMode::LAZY
        && options::bitblastMode.wasSetByUser())
    {
      throwLazyBBUnsupported(m);
    }
    if (!options::bitvectorToBool.wasSetByUser())
    {
      options::bitvectorToBool.set(true);
    }
  }
}

void OptionsHandler::checkBitblastMode(std::string option, BitblastMode m)
{
  if (m == options::BitblastMode::LAZY)
  {
    if (!options::bitvectorPropagate.wasSetByUser())
    {
      options::bitvectorPropagate.set(true);
    }
    if (!options::bitvectorEqualitySolver.wasSetByUser())
    {
      options::bitvectorEqualitySolver.set(true);
    }
    if (!options::bitvectorEqualitySlicer.wasSetByUser())
    {
      if (options::incrementalSolving() || options::produceModels())
      {
        options::bitvectorEqualitySlicer.set(options::BvSlicerMode::OFF);
      }
      else
      {
        options::bitvectorEqualitySlicer.set(options::BvSlicerMode::AUTO);
      }
    }

    if (!options::bitvectorInequalitySolver.wasSetByUser())
    {
      options::bitvectorInequalitySolver.set(true);
    }
    if (!options::bitvectorAlgebraicSolver.wasSetByUser())
    {
      options::bitvectorAlgebraicSolver.set(true);
    }
    if (options::bvSatSolver() != options::SatSolverMode::MINISAT)
    {
      throwLazyBBUnsupported(options::bvSatSolver());
    }
  }
  else if (m == BitblastMode::EAGER)
  {
    if (!options::bitvectorToBool.wasSetByUser())
    {
      options::bitvectorToBool.set(true);
    }
  }
}

void OptionsHandler::setBitblastAig(std::string option, bool arg)
{
  if(arg) {
    if(options::bitblastMode.wasSetByUser()) {
      if (options::bitblastMode() != options::BitblastMode::EAGER)
      {
        throw OptionException("bitblast-aig must be used with eager bitblaster");
      }
    } else {
      options::BitblastMode mode = stringToBitblastMode("", "eager");
      options::bitblastMode.set(mode);
    }
    if(!options::bitvectorAigSimplifications.wasSetByUser()) {
      options::bitvectorAigSimplifications.set("balance;drw");
    }
  }
}

// printer/options_handlers.h
const std::string OptionsHandler::s_instFormatHelp = "\
Inst format modes currently supported by the --inst-format option:\n\
\n\
default \n\
+ Print instantiations as a list in the output language format.\n\
\n\
szs\n\
+ Print instantiations as SZS compliant proof.\n\
";

InstFormatMode OptionsHandler::stringToInstFormatMode(std::string option,
                                                      std::string optarg)
{
  if(optarg == "default") {
    return InstFormatMode::DEFAULT;
  } else if(optarg == "szs") {
    return InstFormatMode::SZS;
  } else if(optarg == "help") {
    puts(s_instFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-format: `") +
                          optarg + "'.  Try --inst-format help.");
  }
}

// decision/options_handlers.h
void OptionsHandler::setDecisionModeStopOnly(std::string option, DecisionMode m)
{
  options::decisionStopOnly.set(m == DecisionMode::RELEVANCY);
}

void OptionsHandler::setProduceAssertions(std::string option, bool value)
{
  options::produceAssertions.set(value);
  options::interactiveMode.set(value);
}

void OptionsHandler::proofEnabledBuild(std::string option, bool value)
{
#ifdef CVC4_PROOF
  if (value && options::bitblastMode() == options::BitblastMode::EAGER
      && options::bvSatSolver() != options::SatSolverMode::MINISAT
      && options::bvSatSolver() != options::SatSolverMode::CRYPTOMINISAT)
  {
    throw OptionException(
        "Eager BV proofs only supported when MiniSat or CryptoMiniSat is used");
  }
#else
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a proofs-enabled build of CVC4; this binary was not built with proof support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_PROOF */
}

void OptionsHandler::LFSCEnabledBuild(std::string option, bool value) {
#ifndef CVC4_USE_LFSC
  if (value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a build of CVC4 with integrated "
                                  "LFSC; this binary was not built with LFSC";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_LFSC */
}

void OptionsHandler::notifyDumpToFile(std::string option) {
  d_options->d_dumpToFileListeners.notify();
}


void OptionsHandler::notifySetRegularOutputChannel(std::string option) {
  d_options->d_setRegularChannelListeners.notify();
}

void OptionsHandler::notifySetDiagnosticOutputChannel(std::string option) {
  d_options->d_setDiagnosticChannelListeners.notify();
}

void OptionsHandler::statsEnabledBuild(std::string option, bool value)
{
#ifndef CVC4_STATISTICS_ON
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a statistics-enabled build of CVC4; this binary was not built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_STATISTICS_ON */
}

void OptionsHandler::threadN(std::string option) {
  throw OptionException(option + " is not a real option by itself.  Use e.g. --thread0=\"--random-seed=10 --random-freq=0.02\" --thread1=\"--random-seed=20 --random-freq=0.05\"");
}

void OptionsHandler::notifyDumpMode(std::string option)
{
  d_options->d_setDumpModeListeners.notify();
}


// expr/options_handlers.h
void OptionsHandler::setDefaultExprDepthPredicate(std::string option, int depth) {
  if(depth < -1) {
    throw OptionException("--expr-depth requires a positive argument, or -1.");
  }
}

void OptionsHandler::setDefaultDagThreshPredicate(std::string option, int dag) {
  if(dag < 0) {
    throw OptionException("--dag-thresh requires a nonnegative argument.");
  }
}

void OptionsHandler::notifySetDefaultExprDepth(std::string option) {
  d_options->d_setDefaultExprDepthListeners.notify();
}

void OptionsHandler::notifySetDefaultDagThresh(std::string option) {
  d_options->d_setDefaultDagThreshListeners.notify();
}

void OptionsHandler::notifySetPrintExprTypes(std::string option) {
  d_options->d_setPrintExprTypesListeners.notify();
}


// main/options_handlers.h

static void print_config (const char * str, std::string config) {
  std::string s(str);
  unsigned sz = 14;
  if (s.size() < sz) s.resize(sz, ' ');
  std::cout << s << ": " << config << std::endl;
}

static void print_config_cond (const char * str, bool cond = false) {
  print_config(str, cond ? "yes" : "no");
}

void OptionsHandler::copyright(std::string option) {
  std::cout << Configuration::copyright() << std::endl;
  exit(0);
}

void OptionsHandler::showConfiguration(std::string option) {
  std::cout << Configuration::about() << std::endl;

  print_config ("version", Configuration::getVersionString());

  if(Configuration::isGitBuild()) {
    const char* branchName = Configuration::getGitBranchName();
    if(*branchName == '\0')  { branchName = "-"; }
    std::stringstream ss;
    ss << "git ["
       << branchName << " "
       << std::string(Configuration::getGitCommit()).substr(0, 8)
       << (Configuration::hasGitModifications() ? " (with modifications)" : "")
       << "]";
    print_config("scm", ss.str());
  } else {
    print_config_cond("scm", false);
  }
  
  std::cout << std::endl;

  std::stringstream ss;
  ss << Configuration::getVersionMajor() << "."
     << Configuration::getVersionMinor() << "."
     << Configuration::getVersionRelease();
  print_config("library", ss.str());
  
  std::cout << std::endl;

  print_config_cond("debug code", Configuration::isDebugBuild());
  print_config_cond("statistics", Configuration::isStatisticsBuild());
  print_config_cond("tracing", Configuration::isTracingBuild());
  print_config_cond("dumping", Configuration::isDumpingBuild());
  print_config_cond("muzzled", Configuration::isMuzzledBuild());
  print_config_cond("assertions", Configuration::isAssertionBuild());
  print_config_cond("proof", Configuration::isProofBuild());
  print_config_cond("coverage", Configuration::isCoverageBuild());
  print_config_cond("profiling", Configuration::isProfilingBuild());
  print_config_cond("asan", Configuration::isAsanBuild());
  print_config_cond("ubsan", Configuration::isUbsanBuild());
  print_config_cond("tsan", Configuration::isTsanBuild());
  print_config_cond("competition", Configuration::isCompetitionBuild());
  
  std::cout << std::endl;
  
  print_config_cond("abc", Configuration::isBuiltWithAbc());
  print_config_cond("cln", Configuration::isBuiltWithCln());
  print_config_cond("glpk", Configuration::isBuiltWithGlpk());
  print_config_cond("cadical", Configuration::isBuiltWithCadical());
  print_config_cond("cryptominisat", Configuration::isBuiltWithCryptominisat());
  print_config_cond("drat2er", Configuration::isBuiltWithDrat2Er());
  print_config_cond("gmp", Configuration::isBuiltWithGmp());
  print_config_cond("kissat", Configuration::isBuiltWithKissat());
  print_config_cond("lfsc", Configuration::isBuiltWithLfsc());
  print_config_cond("readline", Configuration::isBuiltWithReadline());
  print_config_cond("symfpu", Configuration::isBuiltWithSymFPU());
  
  exit(0);
}

static void printTags(unsigned ntags, char const* const* tags)
{
  std::cout << "available tags:";
  for (unsigned i = 0; i < ntags; ++ i)
  {
    std::cout << "  " << tags[i] << std::endl;
  }
  std::cout << std::endl;
}

void OptionsHandler::showDebugTags(std::string option)
{
  if (!Configuration::isDebugBuild())
  {
    throw OptionException("debug tags not available in non-debug builds");
  }
  else if (!Configuration::isTracingBuild())
  {
    throw OptionException("debug tags not available in non-tracing builds");
  }
  printTags(Configuration::getNumDebugTags(),Configuration::getDebugTags());
  exit(0);
}

void OptionsHandler::showTraceTags(std::string option)
{
  if (!Configuration::isTracingBuild())
  {
    throw OptionException("trace tags not available in non-tracing build");
  }
  printTags(Configuration::getNumTraceTags(), Configuration::getTraceTags());
  exit(0);
}

static std::string suggestTags(char const* const* validTags,
                               std::string inputTag,
                               char const* const* additionalTags)
{
  DidYouMean didYouMean;

  const char* opt;
  for (size_t i = 0; (opt = validTags[i]) != nullptr; ++i)
  {
    didYouMean.addWord(validTags[i]);
  }
  if (additionalTags != nullptr)
  {
    for (size_t i = 0; (opt = additionalTags[i]) != nullptr; ++i)
    {
      didYouMean.addWord(additionalTags[i]);
    }
  }

  return didYouMean.getMatchAsString(inputTag);
}

void OptionsHandler::enableTraceTag(std::string option, std::string optarg)
{
  if(!Configuration::isTracingBuild())
  {
    throw OptionException("trace tags not available in non-tracing builds");
  }
  else if(!Configuration::isTraceTag(optarg.c_str()))
  {
    if (optarg == "help")
    {
      printTags(
          Configuration::getNumTraceTags(), Configuration::getTraceTags());
      exit(0);
    }

    throw OptionException(
        std::string("trace tag ") + optarg + std::string(" not available.")
        + suggestTags(Configuration::getTraceTags(), optarg, nullptr));
  }
  Trace.on(optarg);
}

void OptionsHandler::enableDebugTag(std::string option, std::string optarg)
{
  if (!Configuration::isDebugBuild())
  {
    throw OptionException("debug tags not available in non-debug builds");
  }
  else if (!Configuration::isTracingBuild())
  {
    throw OptionException("debug tags not available in non-tracing builds");
  }

  if (!Configuration::isDebugTag(optarg.c_str())
      && !Configuration::isTraceTag(optarg.c_str()))
  {
    if (optarg == "help")
    {
      printTags(
          Configuration::getNumDebugTags(), Configuration::getDebugTags());
      exit(0);
    }

    throw OptionException(std::string("debug tag ") + optarg
                          + std::string(" not available.")
                          + suggestTags(Configuration::getDebugTags(),
                                        optarg,
                                        Configuration::getTraceTags()));
  }
  Debug.on(optarg);
  Trace.on(optarg);
}

OutputLanguage OptionsHandler::stringToOutputLanguage(std::string option,
                                                      std::string optarg)
{
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::output::LANG_AUTO;
  }

  try {
    return language::toOutputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() +
                          "\nTry --output-language help");
  }

  Unreachable();
}

InputLanguage OptionsHandler::stringToInputLanguage(std::string option,
                                                    std::string optarg)
{
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::input::LANG_AUTO;
  }

  try {
    return language::toInputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() + "\nTry --language help");
  }

  Unreachable();
}

/* options/base_options_handlers.h */
void OptionsHandler::setVerbosity(std::string option, int value)
{
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(&CVC4::null_os);
    TraceChannel.setStream(&CVC4::null_os);
    NoticeChannel.setStream(&CVC4::null_os);
    ChatChannel.setStream(&CVC4::null_os);
    MessageChannel.setStream(&CVC4::null_os);
    WarningChannel.setStream(&CVC4::null_os);
  } else {
    if(value < 2) {
      ChatChannel.setStream(&CVC4::null_os);
    } else {
      ChatChannel.setStream(&std::cout);
    }
    if(value < 1) {
      NoticeChannel.setStream(&CVC4::null_os);
    } else {
      NoticeChannel.setStream(&std::cout);
    }
    if(value < 0) {
      MessageChannel.setStream(&CVC4::null_os);
      WarningChannel.setStream(&CVC4::null_os);
    } else {
      MessageChannel.setStream(&std::cout);
      WarningChannel.setStream(&std::cerr);
    }
  }
}

void OptionsHandler::increaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() + 1);
  setVerbosity(option, options::verbosity());
}

void OptionsHandler::decreaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() - 1);
  setVerbosity(option, options::verbosity());
}


}/* CVC4::options namespace */
}/* CVC4 namespace */
