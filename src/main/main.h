/*********************                                                        */
/*! \file main.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Header for main CVC4 driver
 **
 ** Header for main CVC4 driver.
 **/

#include <exception>
#include <string>

#include "util/options.h"
#include "util/exception.h"
#include "util/stats.h"
#include "cvc4autoconfig.h"

#ifndef __CVC4__MAIN__MAIN_H
#define __CVC4__MAIN__MAIN_H

namespace CVC4 {
namespace main {

/** Full argv[0] */
extern const char* progPath;

/** Just the basename component of argv[0] */
extern const char* progName;

/** A reference to the StatisticsRegistry for use by the signal handlers */
extern CVC4::StatisticsRegistry* pStatistics;

/**
 * If true, will not spin on segfault even when CVC4_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.  See util.cpp.
 */
extern bool segvNoSpin;

/** The options currently in play */
extern Options options;

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV. */
void cvc4_init() throw(Exception);

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MAIN__MAIN_H */
