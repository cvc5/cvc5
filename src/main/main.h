/*********************                                                        */
/*! \file main.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Header for main CVC4 driver
 **
 ** Header for main CVC4 driver.
 **/

#include <exception>
#include <string>

#include "base/exception.h"
#include "cvc4autoconfig.h"
#include "expr/expr_manager.h"
#include "options/options.h"
#include "smt/smt_engine.h"
#include "util/statistics.h"
#include "util/statistics_registry.h"

#ifndef CVC4__MAIN__MAIN_H
#define CVC4__MAIN__MAIN_H

namespace CVC4 {
namespace main {

class CommandExecutor;

/** Full argv[0] */
extern const char* progPath;

/** Just the basename component of argv[0] */
extern const std::string* progName;

/** A reference for use by the signal handlers to print statistics */
extern CVC4::main::CommandExecutor* pExecutor;

/** A reference for use by the signal handlers to print statistics */
extern CVC4::TimerStat* pTotalTime;

/**
 * If true, will not spin on segfault even when CVC4_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.  See util.cpp.
 */
extern bool segvSpin;

/** A pointer to the options in play */
extern thread_local Options* pOptions;

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV.
 * This can throw a CVC4::Exception.
 */
void cvc4_init();

/** Shutdown the driver. Frees memory for the signal handlers. */
void cvc4_shutdown() noexcept;

}/* CVC4::main namespace */
}/* CVC4 namespace */

/** Actual Cvc4 driver functions **/
int runCvc4(int argc, char* argv[], CVC4::Options&);
void printUsage(CVC4::Options&, bool full = false);

#endif /* CVC4__MAIN__MAIN_H */
