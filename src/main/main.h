/*********************                                                        */
/*! \file main.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Header for main CVC4 driver
 **
 ** Header for main CVC4 driver.
 **/

#include <exception>
#include <string>

#include "base/tls.h"
#include "base/exception.h"
#include "cvc4autoconfig.h"
#include "expr/expr_manager.h"
#include "options/options.h"
#include "smt/smt_engine.h"
#include "util/statistics.h"
#include "util/statistics_registry.h"

#ifndef __CVC4__MAIN__MAIN_H
#define __CVC4__MAIN__MAIN_H

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
extern CVC4_THREAD_LOCAL Options* pOptions;

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV. */
void cvc4_init() throw(Exception);

/** Shutdown the driver. Frees memory for the signal handlers. */
void cvc4_shutdown() throw();


}/* CVC4::main namespace */
}/* CVC4 namespace */

/** Actual Cvc4 driver functions **/
int runCvc4(int argc, char* argv[], CVC4::Options&);
void printUsage(CVC4::Options&, bool full = false);

#endif /* __CVC4__MAIN__MAIN_H */
