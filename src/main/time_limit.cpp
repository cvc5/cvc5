/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of time limits that are imposed by the --tlimit option.
 *
 * There are various strategies to implement time limits, with different
 * advantages and disadvantages:
 *
 * std::thread: we can spawn a new thread which waits for the time limit.
 * Unless we use std::jthread (from C++20), std::thread is not interruptible
 * and thus we need a synchronization mechanism so that the main thread can
 * communicate to the timer thread that it wants to finish. Apparently, this
 * is the only platform independent way.
 *
 * POSIX setitimer: a very simple way that instructs the kernel to send a
 * signal after some time. If available, this is what we want!
 *
 * Win32 CreateWaitableTimer: unfortunately, this mechanism only calls the
 * completion routine (the callback) when the main thread "enters an
 * alertable wait state", i.e. it sleeps. We don't want our main thread to
 * sleep, thus this approach is not appropriate.
 *
 * Win32 SetTimer: while we can specify a callback function, we still need
 * to process the windows event queue for the callback to be called. (see
 * https://stackoverflow.com/a/15406527/2375725). We don't want our main
 * thread to continuously monitor the event queue.
 *
 *
 * We thus use the setitimer variant whenever possible, and the std::thread
 * variant otherwise.
 */

#include "time_limit.h"

#include "base/cvc5config.h"

#if HAVE_SETITIMER
#include <signal.h>
#include <sys/time.h>
#else
#include <atomic>
#include <chrono>
#include <thread>
#endif

#include <cerrno>
#include <cstring>

#include "base/exception.h"
#include "signal_handlers.h"

namespace cvc5::main {

#if HAVE_SETITIMER
TimeLimit::~TimeLimit() {}

void posix_timeout_handler(int sig, siginfo_t* info, void*)
{
  signal_handlers::timeout_handler();
}
#else
std::atomic<bool> abort_timer_flag;

TimeLimit::~TimeLimit()
{
  abort_timer_flag.store(true);
}
#endif

TimeLimit install_time_limit(uint64_t ms)
{
  // Skip if no time limit shall be set.
  if (ms == 0) {
    return TimeLimit();
  }

#if HAVE_SETITIMER
  // Install a signal handler for SIGALRM
  struct sigaction sact;
  sact.sa_sigaction = posix_timeout_handler;
  sact.sa_flags = SA_SIGINFO;
  sigemptyset(&sact.sa_mask);
  if (sigaction(SIGALRM, &sact, NULL))
  {
    throw internal::Exception(std::string("sigaction(SIGALRM) failure: ")
                              + strerror(errno));
  }

  // Check https://linux.die.net/man/2/setitimer
  // Then time is up, the kernel will send a SIGALRM
  struct itimerval timerspec;
  timerspec.it_value.tv_sec = ms / 1000;
  timerspec.it_value.tv_usec = (ms % 1000) * 1000;
  timerspec.it_interval.tv_sec = 0;
  timerspec.it_interval.tv_usec = 0;
  // Argument 1: which timer to set, we want the real time
  // Argument 2: timer configuration, relative to current time
  // Argument 3: old timer configuration, we don't want to know
  if (setitimer(ITIMER_REAL, &timerspec, nullptr))
  {
    throw internal::Exception(std::string("timer_settime() failure: ")
                              + strerror(errno));
  }
#else
  abort_timer_flag.store(false);
  std::thread t([ms]()
  {
    // when to stop
    auto limit = std::chrono::system_clock::now() + std::chrono::milliseconds(ms);
    while (limit > std::chrono::system_clock::now())
    {
      // check if the main thread is done
      if (abort_timer_flag.load()) return;
      std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
    // trigger the timeout handler
    signal_handlers::timeout_handler();
  });
  // detach the thread
  t.detach();
#endif
  return TimeLimit();
}

}  // namespace cvc5::main
