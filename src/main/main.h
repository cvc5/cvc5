/*********************                                                        */
/*! \file main.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Header for main CVC4 driver
 **
 ** Header for main CVC4 driver.
 **/

#include <exception>
#include <string>

#include "options/options.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "util/exception.h"
#include "util/statistics.h"
#include "util/tls.h"
#include "util/statistics_registry.h"
#include "cvc4autoconfig.h"

#ifndef __CVC4__MAIN__MAIN_H
#define __CVC4__MAIN__MAIN_H

namespace CVC4 {
namespace main {

class CommandExecutor;

/** Full argv[0] */
extern const char* progPath;

/** Just the basename component of argv[0] */
extern const char* progName;

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
extern CVC4_THREADLOCAL(Options*) pOptions;

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV. */
void cvc4_init() throw(Exception);

}/* CVC4::main namespace */
}/* CVC4 namespace */

/** Actual Cvc4 driver functions **/
int runCvc4(int argc, char* argv[], CVC4::Options&);
void printUsage(CVC4::Options&, bool full = false);

#endif /* __CVC4__MAIN__MAIN_H */
