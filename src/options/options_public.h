/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Public facing functions for options that need to be accessed from the
 * outside.
 *
 * These are all 1 line wrappers for `Options::operator[]`, `Options::set()` and
 * `Options::wasSetByUser()` so that external code (including parser/ and main/)
 * does not need to include the option modules (*_options.h).
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_PUBLIC_H
#define CVC5__OPTIONS__OPTIONS_PUBLIC_H

#include "options/language.h"
#include "options/options.h"
#include "options/printer_modes.h"

namespace cvc5::options {

InputLanguage getInputLanguage(const Options& opts) CVC5_EXPORT;
InstFormatMode getInstFormatMode(const Options& opts) CVC5_EXPORT;
OutputLanguage getOutputLanguage(const Options& opts) CVC5_EXPORT;
bool getUfHo(const Options& opts) CVC5_EXPORT;
bool getDumpInstantiations(const Options& opts) CVC5_EXPORT;
bool getDumpModels(const Options& opts) CVC5_EXPORT;
bool getDumpProofs(const Options& opts) CVC5_EXPORT;
bool getDumpUnsatCores(const Options& opts) CVC5_EXPORT;
bool getEarlyExit(const Options& opts) CVC5_EXPORT;
bool getFilesystemAccess(const Options& opts) CVC5_EXPORT;
bool getForceNoLimitCpuWhileDump(const Options& opts) CVC5_EXPORT;
bool getHelp(const Options& opts) CVC5_EXPORT;
bool getIncrementalSolving(const Options& opts) CVC5_EXPORT;
bool getInteractive(const Options& opts) CVC5_EXPORT;
bool getInteractivePrompt(const Options& opts) CVC5_EXPORT;
bool getLanguageHelp(const Options& opts) CVC5_EXPORT;
bool getMemoryMap(const Options& opts) CVC5_EXPORT;
bool getParseOnly(const Options& opts) CVC5_EXPORT;
bool getProduceModels(const Options& opts) CVC5_EXPORT;
bool getSegvSpin(const Options& opts) CVC5_EXPORT;
bool getSemanticChecks(const Options& opts) CVC5_EXPORT;
bool getStatistics(const Options& opts) CVC5_EXPORT;
bool getStatsEveryQuery(const Options& opts) CVC5_EXPORT;
bool getStrictParsing(const Options& opts) CVC5_EXPORT;
int32_t getTearDownIncremental(const Options& opts) CVC5_EXPORT;
uint64_t getCumulativeTimeLimit(const Options& opts) CVC5_EXPORT;
bool getVersion(const Options& opts) CVC5_EXPORT;
const std::string& getForceLogicString(const Options& opts) CVC5_EXPORT;
int32_t getVerbosity(const Options& opts) CVC5_EXPORT;

std::istream* getIn(const Options& opts) CVC5_EXPORT;
std::ostream* getErr(const Options& opts) CVC5_EXPORT;
std::ostream* getOut(const Options& opts) CVC5_EXPORT;
const std::string& getBinaryName(const Options& opts) CVC5_EXPORT;

void setInputLanguage(InputLanguage val, Options& opts) CVC5_EXPORT;
void setInteractive(bool val, Options& opts) CVC5_EXPORT;
void setOut(std::ostream* val, Options& opts) CVC5_EXPORT;
void setOutputLanguage(OutputLanguage val, Options& opts) CVC5_EXPORT;

bool wasSetByUserEarlyExit(const Options& opts) CVC5_EXPORT;
bool wasSetByUserForceLogicString(const Options& opts) CVC5_EXPORT;
bool wasSetByUserIncrementalSolving(const Options& opts) CVC5_EXPORT;
bool wasSetByUserInteractive(const Options& opts) CVC5_EXPORT;

}  // namespace cvc5::options

#endif
