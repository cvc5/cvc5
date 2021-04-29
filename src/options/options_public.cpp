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
 * Definitions of public facing interface functions for Options.
 *
 * These are all 1 line wrappers for Options::get<T>, Options::set<T>, and
 * Options::wasSetByUser<T> for different option types T.
 */

#include "options_public.h"

#include <fstream>
#include <ostream>
#include <string>
#include <vector>

#include "base/listener.h"
#include "base/modal_exception.h"
#include "options.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/parser_options.h"
#include "options/printer_modes.h"
#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/resource_manager_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"

namespace cvc5::options {

InputLanguage getInputLanguage(const Options& opts)
{
  return opts[options::inputLanguage];
}
InstFormatMode getInstFormatMode(const Options& opts)
{
  return opts[options::instFormatMode];
}
OutputLanguage getOutputLanguage(const Options& opts)
{
  return opts[options::outputLanguage];
}
bool getUfHo(const Options& opts) { return opts[options::ufHo]; }
bool getDumpInstantiations(const Options& opts)
{
  return opts[options::dumpInstantiations];
}
bool getDumpModels(const Options& opts) { return opts[options::dumpModels]; }
bool getDumpProofs(const Options& opts) { return opts[options::dumpProofs]; }
bool getDumpUnsatCores(const Options& opts)
{
  return opts[options::dumpUnsatCores] || opts[options::dumpUnsatCoresFull];
}
bool getEarlyExit(const Options& opts) { return opts[options::earlyExit]; }
bool getFilesystemAccess(const Options& opts)
{
  return opts[options::filesystemAccess];
}
bool getForceNoLimitCpuWhileDump(const Options& opts)
{
  return opts[options::forceNoLimitCpuWhileDump];
}
bool getHelp(const Options& opts) { return opts[options::help]; }
bool getIncrementalSolving(const Options& opts)
{
  return opts[options::incrementalSolving];
}
bool getInteractive(const Options& opts) { return opts[options::interactive]; }
bool getInteractivePrompt(const Options& opts)
{
  return opts[options::interactivePrompt];
}
bool getLanguageHelp(const Options& opts)
{
  return opts[options::languageHelp];
}
bool getMemoryMap(const Options& opts) { return opts[options::memoryMap]; }
bool getParseOnly(const Options& opts) { return opts[options::parseOnly]; }
bool getProduceModels(const Options& opts)
{
  return opts[options::produceModels];
}
bool getSegvSpin(const Options& opts) { return opts[options::segvSpin]; }
bool getSemanticChecks(const Options& opts)
{
  return opts[options::semanticChecks];
}
bool getStatistics(const Options& opts) { return opts[options::statistics]; }
bool getStatsEveryQuery(const Options& opts)
{
  return opts[options::statisticsEveryQuery];
}
bool getStrictParsing(const Options& opts)
{
  return opts[options::strictParsing];
}
int getTearDownIncremental(const Options& opts)
{
  return opts[options::tearDownIncremental];
}
unsigned long getCumulativeTimeLimit(const Options& opts)
{
  return opts[options::cumulativeMillisecondLimit];
}
bool getVersion(const Options& opts) { return opts[options::version]; }
const std::string& getForceLogicString(const Options& opts)
{
  return opts[options::forceLogicString];
}
int getVerbosity(const Options& opts) { return opts[options::verbosity]; }

std::istream* getIn(const Options& opts) { return opts[options::in]; }
std::ostream* getErr(const Options& opts) { return opts[options::err]; }
std::ostream* getOut(const Options& opts) { return opts[options::out]; }
const std::string& getBinaryName(const Options& opts)
{
  return opts[options::binary_name];
}

void setInputLanguage(InputLanguage val, Options& opts)
{
  opts.set(options::inputLanguage, val);
}
void setInteractive(bool val, Options& opts)
{
  opts.set(options::interactive, val);
}
void setOut(std::ostream* val, Options& opts) { opts.set(options::out, val); }
void setOutputLanguage(OutputLanguage val, Options& opts)
{
  opts.set(options::outputLanguage, val);
}

bool wasSetByUserEarlyExit(const Options& opts)
{
  return opts.wasSetByUser(options::earlyExit);
}
bool wasSetByUserForceLogicString(const Options& opts)
{
  return opts.wasSetByUser(options::forceLogicString);
}
bool wasSetByUserIncrementalSolving(const Options& opts)
{
  return opts.wasSetByUser(options::incrementalSolving);
}
bool wasSetByUserInteractive(const Options& opts)
{
  return opts.wasSetByUser(options::interactive);
}

}  // namespace cvc5::options
