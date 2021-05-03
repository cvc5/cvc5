/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Header for main cvc5 driver.
 */

#include <chrono>
#include <exception>
#include <memory>
#include <string>

#include "base/cvc5config.h"
#include "base/exception.h"
#include "options/options.h"

#ifndef CVC5__MAIN__MAIN_H
#define CVC5__MAIN__MAIN_H

namespace cvc5 {
namespace main {

class CommandExecutor;

/** Full argv[0] */
extern const char* progPath;

/** Just the basename component of argv[0] */
extern const std::string* progName;

/** A reference for use by the signal handlers to print statistics */
extern std::unique_ptr<cvc5::main::CommandExecutor> pExecutor;

/** Manages a custom timer for the total runtime in RAII-style. */
class TotalTimer
{
 public:
  TotalTimer() : d_start(std::chrono::steady_clock::now()) {}
  ~TotalTimer();

 private:
  std::chrono::steady_clock::time_point d_start;
};
/** The time point the binary started, accessible to signal handlers */
extern std::unique_ptr<TotalTimer> totalTime;

/**
 * If true, will not spin on segfault even when CVC5_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.  See util.cpp.
 */
extern bool segvSpin;

/** A pointer to the options in play */
extern thread_local Options* pOptions;

}  // namespace main
}  // namespace cvc5

/** Actual cvc5 driver functions **/
int runCvc5(int argc, char* argv[], cvc5::Options&);
void printUsage(cvc5::Options&, bool full = false);

#endif /* CVC5__MAIN__MAIN_H */
