/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of signal handlers.
 *
 * It is important to only call async-signal-safe functions from signal
 * handlers. See: http://man7.org/linux/man-pages/man7/signal-safety.7.html for
 * a list of async-signal-safe POSIX.1 functions.
 */

#include <string.h>

#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <exception>

#ifndef __WIN32__

#include <signal.h>
#include <sys/resource.h>
#include <unistd.h>

#endif /* __WIN32__ */

#include "base/cvc5config.h"
#include "base/exception.h"
#include "main/command_executor.h"
#include "main/main.h"
#include "util/safe_print.h"

using cvc5::internal::Exception;
using namespace std;

namespace cvc5::main {
using namespace cvc5::internal;

/**
 * If true, will not spin on segfault even when CVC5_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.
 */
bool segvSpin = false;

namespace signal_handlers {

void print_statistics()
{
  if (pExecutor != nullptr)
  {
    pExecutor->printStatisticsSafe(STDERR_FILENO);
  }
}

void timeout_handler()
{
  safe_print(STDERR_FILENO, "cvc5 interrupted by timeout.\n");
  print_statistics();
  abort();
}

#ifndef __WIN32__

#ifdef HAVE_SIGALTSTACK
size_t stackSize;
void* stackBase;
#endif /* HAVE_SIGALTSTACK */

/** Handler for SIGXCPU and SIGALRM, i.e., timeout. */
void timeout_handler(int sig, siginfo_t* info, void*) { timeout_handler(); }

/** Handler for SIGTERM. */
void sigterm_handler(int sig, siginfo_t* info, void*)
{
  safe_print(STDERR_FILENO, "cvc5 interrupted by SIGTERM.\n");
  print_statistics();
  signal(sig, SIG_DFL);
  raise(sig);
}

/** Handler for SIGINT, i.e., when the user hits control C. */
void sigint_handler(int sig, siginfo_t* info, void*)
{
  safe_print(STDERR_FILENO, "cvc5 interrupted by user.\n");
  print_statistics();
  signal(sig, SIG_DFL);
  raise(sig);
}

#ifdef HAVE_SIGALTSTACK
/** Handler for SIGSEGV (segfault). */
void segv_handler(int sig, siginfo_t* info, void* c)
{
  uintptr_t extent = reinterpret_cast<uintptr_t>(stackBase) - stackSize;
  uintptr_t addr = reinterpret_cast<uintptr_t>(info->si_addr);
#ifdef CVC5_DEBUG
  safe_print(STDERR_FILENO, "cvc5 suffered a segfault in DEBUG mode.\n");
  safe_print(STDERR_FILENO, "Offending address is ");
  safe_print(STDERR_FILENO, info->si_addr);
  safe_print(STDERR_FILENO, "\n");
  // cerr << "base is " << (void*)stackBase << endl;
  // cerr << "size is " << stackSize << endl;
  // cerr << "extent is " << (void*)extent << endl;
  if (addr >= extent && addr <= extent + 10 * 1024)
  {
    safe_print(STDERR_FILENO,
               "Looks like this is likely due to stack overflow.\n");
    safe_print(STDERR_FILENO,
               "You might consider increasing the limit with `ulimit -s' or "
               "equivalent.\n");
  }
  else if (addr < 10 * 1024)
  {
    safe_print(STDERR_FILENO, "Looks like a NULL pointer was dereferenced.\n");
  }

  if (!segvSpin)
  {
    print_statistics();
    signal(sig, SIG_DFL);
    raise(sig);
  }
  else
  {
    safe_print(STDERR_FILENO,
               "Spinning so that a debugger can be connected.\n");
    safe_print(STDERR_FILENO, "Try:  gdb ");
    safe_print(STDERR_FILENO, progName);
    safe_print(STDERR_FILENO, " ");
    safe_print<int64_t>(STDERR_FILENO, getpid());
    safe_print(STDERR_FILENO, "\n");
    safe_print(STDERR_FILENO, " or:  gdb --pid=");
    safe_print<int64_t>(STDERR_FILENO, getpid());
    safe_print(STDERR_FILENO, " ");
    safe_print(STDERR_FILENO, progName);
    safe_print(STDERR_FILENO, "\n");
    for (;;)
    {
      sleep(60);
    }
  }
#else  /* CVC5_DEBUG */
  safe_print(STDERR_FILENO, "cvc5 suffered a segfault.\n");
  safe_print(STDERR_FILENO, "Offending address is ");
  safe_print(STDERR_FILENO, info->si_addr);
  safe_print(STDERR_FILENO, "\n");
  if (addr >= extent && addr <= extent + 10 * 1024)
  {
    safe_print(STDERR_FILENO,
               "Looks like this is likely due to stack overflow.\n");
    safe_print(STDERR_FILENO,
               "You might consider increasing the limit with `ulimit -s' or "
               "equivalent.\n");
  }
  else if (addr < 10 * 1024)
  {
    safe_print(STDERR_FILENO, "Looks like a NULL pointer was dereferenced.\n");
  }
  print_statistics();
  signal(sig, SIG_DFL);
  raise(sig);
#endif /* CVC5_DEBUG */
}
#endif /* HAVE_SIGALTSTACK */

/** Handler for SIGILL (illegal instruction). */
void ill_handler(int sig, siginfo_t* info, void*)
{
#ifdef CVC5_DEBUG
  safe_print(STDERR_FILENO,
             "cvc5 executed an illegal instruction in DEBUG mode.\n");
  if (!segvSpin)
  {
    print_statistics();
    signal(sig, SIG_DFL);
    raise(sig);
  }
  else
  {
    safe_print(STDERR_FILENO,
               "Spinning so that a debugger can be connected.\n");
    safe_print(STDERR_FILENO, "Try:  gdb ");
    safe_print(STDERR_FILENO, progName);
    safe_print(STDERR_FILENO, " ");
    safe_print<int64_t>(STDERR_FILENO, getpid());
    safe_print(STDERR_FILENO, "\n");
    safe_print(STDERR_FILENO, " or:  gdb --pid=");
    safe_print<int64_t>(STDERR_FILENO, getpid());
    safe_print(STDERR_FILENO, " ");
    safe_print(STDERR_FILENO, progName);
    safe_print(STDERR_FILENO, "\n");
    for (;;)
    {
      sleep(60);
    }
  }
#else  /* CVC5_DEBUG */
  safe_print(STDERR_FILENO, "cvc5 executed an illegal instruction.\n");
  print_statistics();
  signal(sig, SIG_DFL);
  raise(sig);
#endif /* CVC5_DEBUG */
}

#endif /* __WIN32__ */

static terminate_handler default_terminator;

void cvc5terminate()
{
  set_terminate(default_terminator);
#ifdef CVC5_DEBUG
  LastExceptionBuffer* current = LastExceptionBuffer::getCurrent();
  LastExceptionBuffer::setCurrent(NULL);
  delete current;

  safe_print(STDERR_FILENO,
             "\n"
             "cvc5 was terminated by the C++ runtime.\n"
             "Perhaps an exception was thrown during stack unwinding.  "
             "(Don't do that.)\n");
  print_statistics();
  default_terminator();
#else  /* CVC5_DEBUG */
  safe_print(STDERR_FILENO,
             "cvc5 was terminated by the C++ runtime.\n"
             "Perhaps an exception was thrown during stack unwinding.\n");
  print_statistics();
  default_terminator();
#endif /* CVC5_DEBUG */
}

void install()
{
#ifdef CVC5_DEBUG
  LastExceptionBuffer::setCurrent(new LastExceptionBuffer());
#endif

#ifndef __WIN32__
  struct rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit))
  {
    throw Exception(string("getrlimit() failure: ") + strerror(errno));
  }
  if (limit.rlim_cur != limit.rlim_max)
  {
    limit.rlim_cur = limit.rlim_max;
    if (setrlimit(RLIMIT_STACK, &limit))
    {
      throw Exception(string("setrlimit() failure: ") + strerror(errno));
    }
    if (getrlimit(RLIMIT_STACK, &limit))
    {
      throw Exception(string("getrlimit() failure: ") + strerror(errno));
    }
  }

  struct sigaction act1;
  act1.sa_sigaction = sigint_handler;
  act1.sa_flags = SA_SIGINFO;
  sigemptyset(&act1.sa_mask);
  if (sigaction(SIGINT, &act1, NULL))
  {
    throw Exception(string("sigaction(SIGINT) failure: ") + strerror(errno));
  }

  struct sigaction act2;
  act2.sa_sigaction = timeout_handler;
  act2.sa_flags = SA_SIGINFO;
  sigemptyset(&act2.sa_mask);
  if (sigaction(SIGXCPU, &act2, NULL))
  {
    throw Exception(string("sigaction(SIGXCPU) failure: ") + strerror(errno));
  }

  struct sigaction act3;
  act3.sa_sigaction = ill_handler;
  act3.sa_flags = SA_SIGINFO;
  sigemptyset(&act3.sa_mask);
  if (sigaction(SIGILL, &act3, NULL))
  {
    throw Exception(string("sigaction(SIGILL) failure: ") + strerror(errno));
  }

#ifdef HAVE_SIGALTSTACK
  stack_t ss;
  ss.ss_sp = (char*)malloc(SIGSTKSZ);
  if (ss.ss_sp == NULL)
  {
    throw Exception("Can't malloc() space for a signal stack");
  }
  ss.ss_size = SIGSTKSZ;
  ss.ss_flags = 0;
  if (sigaltstack(&ss, NULL) == -1)
  {
    throw Exception(string("sigaltstack() failure: ") + strerror(errno));
  }

  stackSize = limit.rlim_cur;
  stackBase = ss.ss_sp;

  struct sigaction act4;
  act4.sa_sigaction = segv_handler;
  act4.sa_flags = SA_SIGINFO | SA_ONSTACK;
  sigemptyset(&act4.sa_mask);
  if (sigaction(SIGSEGV, &act4, NULL))
  {
    throw Exception(string("sigaction(SIGSEGV) failure: ") + strerror(errno));
  }
#endif /* HAVE_SIGALTSTACK */

  struct sigaction act5;
  act5.sa_sigaction = sigterm_handler;
  act5.sa_flags = SA_SIGINFO;
  sigemptyset(&act5.sa_mask);
  if (sigaction(SIGTERM, &act5, NULL))
  {
    throw Exception(string("sigaction(SIGTERM) failure: ") + strerror(errno));
  }

#endif /* __WIN32__ */

  default_terminator = set_terminate(cvc5terminate);
}

void cleanup() noexcept
{
#ifndef __WIN32__
#ifdef HAVE_SIGALTSTACK
  free(stackBase);
  stackBase = nullptr;
  stackSize = 0;
#endif /* HAVE_SIGALTSTACK */
#endif /* __WIN32__ */
}

}  // namespace signal_handlers
}  // namespace cvc5::main
