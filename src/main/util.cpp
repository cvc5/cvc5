/*********************                                           -*- C++ -*-  */
/** util.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Utilities for the main driver.
 **/

#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <string.h>
#include <signal.h>

#include "util/exception.h"
#include "config.h"

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

/** Handler for SIGINT, i.e., when the user hits control C. */
void sigint_handler(int sig, siginfo_t* info, void*) {
  fprintf(stderr, "CVC4 interrupted by user.\n");
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

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV. */
void cvc4_init() throw() {
  struct sigaction act1;
  act1.sa_sigaction = sigint_handler;
  act1.sa_flags = SA_SIGINFO;
  sigemptyset(&act1.sa_mask);
  if(sigaction(SIGINT, &act1, NULL))
    throw Exception(string("sigaction(SIGINT) failure: ") + strerror(errno));

  struct sigaction act2;
  act2.sa_sigaction = segv_handler;
  act2.sa_flags = SA_SIGINFO;
  sigemptyset(&act2.sa_mask);
  if(sigaction(SIGSEGV, &act2, NULL))
    throw Exception(string("sigaction(SIGSEGV) failure: ") + strerror(errno));
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
