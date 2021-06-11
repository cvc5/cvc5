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
 * These are all one line wrappers for accessing the internal option data.
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
  return opts.base.inputLanguage;
}
InstFormatMode getInstFormatMode(const Options& opts)
{
  return opts.printer.instFormatMode;
}
OutputLanguage getOutputLanguage(const Options& opts)
{
  return opts.base.outputLanguage;
}
bool getUfHo(const Options& opts) { return opts.uf.ufHo; }
bool getDumpInstantiations(const Options& opts)
{
  return opts.smt.dumpInstantiations;
}
bool getDumpModels(const Options& opts) { return opts.smt.dumpModels; }
bool getDumpProofs(const Options& opts) { return opts.smt.dumpProofs; }
bool getDumpUnsatCores(const Options& opts)
{
  return opts.smt.dumpUnsatCores || opts.smt.dumpUnsatCoresFull;
}
bool getFilesystemAccess(const Options& opts)
{
  return opts.parser.filesystemAccess;
}
bool getForceNoLimitCpuWhileDump(const Options& opts)
{
  return opts.smt.forceNoLimitCpuWhileDump;
}
bool getIncrementalSolving(const Options& opts)
{
  return opts.smt.incrementalSolving;
}
bool getLanguageHelp(const Options& opts) { return opts.base.languageHelp; }
bool getMemoryMap(const Options& opts) { return opts.parser.memoryMap; }
bool getParseOnly(const Options& opts) { return opts.base.parseOnly; }
bool getProduceModels(const Options& opts) { return opts.smt.produceModels; }
bool getSemanticChecks(const Options& opts)
{
  return opts.parser.semanticChecks;
}
bool getStatistics(const Options& opts) { return opts.base.statistics; }
bool getStatsEveryQuery(const Options& opts)
{
  return opts.base.statisticsEveryQuery;
}
bool getStrictParsing(const Options& opts)
{
  return opts.parser.strictParsing;
}
uint64_t getCumulativeTimeLimit(const Options& opts)
{
  return opts.resman.cumulativeMillisecondLimit;
}
const std::string& getForceLogicString(const Options& opts)
{
  return opts.parser.forceLogicString;
}
int32_t getVerbosity(const Options& opts) { return opts.base.verbosity; }

std::istream* getIn(const Options& opts) { return opts.base.in; }
std::ostream* getErr(const Options& opts) { return opts.base.err; }
std::ostream* getOut(const Options& opts) { return opts.base.out; }

void setInputLanguage(InputLanguage val, Options& opts)
{
  opts.base.inputLanguage = val;
}
void setOut(std::ostream* val, Options& opts) { opts.base.out = val; }
void setOutputLanguage(OutputLanguage val, Options& opts)
{
  opts.base.outputLanguage = val;
}

bool wasSetByUserEarlyExit(const Options& opts)
{
  return opts.driver.earlyExitWasSetByUser;
}
bool wasSetByUserForceLogicString(const Options& opts)
{
  return opts.parser.forceLogicStringWasSetByUser;
}
bool wasSetByUserIncrementalSolving(const Options& opts)
{
  return opts.smt.incrementalSolvingWasSetByUser;
}
bool wasSetByUserInteractive(const Options& opts)
{
  return opts.driver.interactiveWasSetByUser;
}

}  // namespace cvc5::options
