/*********************                                                        */
/*! \file util.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Utilities for the main driver.
 **
 ** Utilities for the main driver.
 **/

#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <exception>
#include <string.h>
#include <signal.h>

#include "util/exception.h"
#include "util/options.h"
#include "util/Assert.h"
#include "util/stats.h"

#include "cvc4autoconfig.h"
#include "main.h"

using CVC4::Exception;
using namespace std;

namespace CVC4 {
namespace main {

/**
 * If true, will not spin on segfault even when CVC4_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.
 */
bool segvNoSpin = false;

/** Handler for SIGXCPU, i.e., timeout. */
void timeout_handler(int sig, siginfo_t* info, void*) {
  fprintf(stderr, "CVC4 interrupted by timeout.\n");
  if(options.statistics) {
    StatisticsRegistry::flushStatistics(cerr);
  }
  abort();
}

/** Handler for SIGINT, i.e., when the user hits control C. */
void sigint_handler(int sig, siginfo_t* info, void*) {
  fprintf(stderr, "CVC4 interrupted by user.\n");
  if(options.statistics) {
    StatisticsRegistry::flushStatistics(cerr);
  }
  abort();
}

/** Handler for SIGSEGV (segfault). */
void segv_handler(int sig, siginfo_t* info, void*) {
#ifdef CVC4_DEBUG
  fprintf(stderr, "CVC4 suffered a segfault in DEBUG mode.\n");
  if(segvNoSpin) {
    fprintf(stderr, "No-spin requested, aborting...\n");
    abort();
  } else {
    fprintf(stderr, "Spinning so that a debugger can be connected.\n");
    fprintf(stderr, "Try:  gdb %s %u\n", progName, getpid());
    for(;;) {
      sleep(60);
    }
  }
#else /* CVC4_DEBUG */
  fprintf(stderr, "CVC4 suffered a segfault.\n");
  abort();
#endif /* CVC4_DEBUG */
}

static terminate_handler default_terminator;

void cvc4unexpected() {
#ifdef CVC4_DEBUG
  fprintf(stderr, "\n"
          "CVC4 threw an \"unexpected\" exception (one that wasn't properly "
          "specified\nin the throws() specifier for the throwing function)."
          "\n\n");
  if(CVC4::s_debugLastException == NULL) {
    fprintf(stderr,
            "The exception is unknown (maybe it's not a CVC4::Exception).\n\n");
  } else {
    fprintf(stderr, "The exception is:\n%s\n\n", CVC4::s_debugLastException);
  }
  if(segvNoSpin) {
    fprintf(stderr, "No-spin requested.\n");
    set_terminate(default_terminator);
  } else {
    fprintf(stderr, "Spinning so that a debugger can be connected.\n");
    fprintf(stderr, "Try:  gdb %s %u\n", progName, getpid());
    for(;;) {
      sleep(60);
    }
  }
#else /* CVC4_DEBUG */
  fprintf(stderr, "CVC4 threw an \"unexpected\" exception.\n");
  set_terminate(default_terminator);
#endif /* CVC4_DEBUG */
}

void cvc4terminate() {
#ifdef CVC4_DEBUG
  fprintf(stderr, "\n"
          "CVC4 was terminated by the C++ runtime.\n"
          "Perhaps an exception was thrown during stack unwinding.  "
          "(Don't do that.)\n");
  default_terminator();
#else /* CVC4_DEBUG */
  fprintf(stderr,
          "CVC4 was terminated by the C++ runtime.\n"
          "Perhaps an exception was thrown during stack unwinding.\n");
  default_terminator();
#endif /* CVC4_DEBUG */
}

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV. */
void cvc4_init() throw() {
  struct sigaction act1;
  act1.sa_sigaction = sigint_handler;
  act1.sa_flags = SA_SIGINFO;
  sigemptyset(&act1.sa_mask);
  if(sigaction(SIGINT, &act1, NULL))
    throw Exception(string("sigaction(SIGINT) failure: ") + strerror(errno));

  struct sigaction act2;
  act2.sa_sigaction = timeout_handler;
  act2.sa_flags = SA_SIGINFO;
  sigemptyset(&act2.sa_mask);
  if(sigaction(SIGXCPU, &act2, NULL))
    throw Exception(string("sigaction(SIGXCPU) failure: ") + strerror(errno));

  struct sigaction act3;
  act3.sa_sigaction = segv_handler;
  act3.sa_flags = SA_SIGINFO;
  sigemptyset(&act3.sa_mask);
  if(sigaction(SIGSEGV, &act3, NULL))
    throw Exception(string("sigaction(SIGSEGV) failure: ") + strerror(errno));

  set_unexpected(cvc4unexpected);
  default_terminator = set_terminate(cvc4terminate);
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
