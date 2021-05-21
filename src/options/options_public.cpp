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
#include "options/base_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/parser_options.h"
#include "options/printer_modes.h"
#include "options/printer_options.h"
#include "options/resource_manager_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"

namespace cvc5::options {

InputLanguage getInputLanguage(const Options& opts)
{
  return opts.base().inputLanguage;
}
InstFormatMode getInstFormatMode(const Options& opts)
{
  return opts.printer().instFormatMode;
}
OutputLanguage getOutputLanguage(const Options& opts)
{
  return opts.base().outputLanguage;
}
bool getUfHo(const Options& opts) { return opts.uf().ufHo; }
bool getDumpInstantiations(const Options& opts)
{
  return opts.smt().dumpInstantiations;
}
bool getDumpModels(const Options& opts) { return opts.smt().dumpModels; }
bool getDumpProofs(const Options& opts) { return opts.smt().dumpProofs; }
bool getDumpUnsatCores(const Options& opts)
{
  return opts.smt().dumpUnsatCores || opts.smt().dumpUnsatCoresFull;
}
bool getEarlyExit(const Options& opts) { return opts.driver().earlyExit; }
bool getFilesystemAccess(const Options& opts)
{
  return opts.parser().filesystemAccess;
}
bool getForceNoLimitCpuWhileDump(const Options& opts)
{
  return opts.smt().forceNoLimitCpuWhileDump;
}
bool getHelp(const Options& opts) { return opts.driver().help; }
bool getIncrementalSolving(const Options& opts)
{
  return opts.smt().incrementalSolving;
}
bool getInteractive(const Options& opts) { return opts.driver().interactive; }
bool getInteractivePrompt(const Options& opts)
{
  return opts.driver().interactivePrompt;
}
bool getLanguageHelp(const Options& opts) { return opts.base().languageHelp; }
bool getMemoryMap(const Options& opts) { return opts.parser().memoryMap; }
bool getParseOnly(const Options& opts) { return opts.base().parseOnly; }
bool getProduceModels(const Options& opts) { return opts.smt().produceModels; }
bool getSegvSpin(const Options& opts) { return opts.driver().segvSpin; }
bool getSemanticChecks(const Options& opts)
{
  return opts.parser().semanticChecks;
}
bool getStatistics(const Options& opts) { return opts.base().statistics; }
bool getStatsEveryQuery(const Options& opts)
{
  return opts.base().statisticsEveryQuery;
}
bool getStrictParsing(const Options& opts)
{
  return opts.parser().strictParsing;
}
int getTearDownIncremental(const Options& opts)
{
  return opts.driver().tearDownIncremental;
}
unsigned long getCumulativeTimeLimit(const Options& opts)
{
  return opts.resman().cumulativeMillisecondLimit;
}
bool getVersion(const Options& opts) { return opts.driver().version; }
const std::string& getForceLogicString(const Options& opts)
{
  return opts.parser().forceLogicString;
}
int getVerbosity(const Options& opts) { return opts.base().verbosity; }

std::istream* getIn(const Options& opts) { return opts.base().in; }
std::ostream* getErr(const Options& opts) { return opts.base().err; }
std::ostream* getOut(const Options& opts) { return opts.base().out; }
const std::string& getBinaryName(const Options& opts)
{
  return opts.base().binary_name;
}

void setInputLanguage(InputLanguage val, Options& opts)
{
  opts.base().inputLanguage = val;
}
void setInteractive(bool val, Options& opts)
{
  opts.driver().interactive = val;
}
void setOut(std::ostream* val, Options& opts) { opts.base().out = val; }
void setOutputLanguage(OutputLanguage val, Options& opts)
{
  opts.base().outputLanguage = val;
}

bool wasSetByUserEarlyExit(const Options& opts)
{
  return opts.driver().earlyExit__setByUser__;
}
bool wasSetByUserForceLogicString(const Options& opts)
{
  return opts.parser().forceLogicString__setByUser__;
}
bool wasSetByUserIncrementalSolving(const Options& opts)
{
  return opts.smt().incrementalSolving__setByUser__;
}
bool wasSetByUserInteractive(const Options& opts)
{
  return opts.driver().interactive__setByUser__;
}

}  // namespace cvc5::options
