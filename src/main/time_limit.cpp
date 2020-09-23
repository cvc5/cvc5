/*********************                                                        */
/*! \file time_limit.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of time limits.
 **
 ** Implementation of time limits that are imposed by the --tlimit option.
 **/

#include "time_limit.h"

#if defined(__MINGW32__) || defined(__MINGW64__)
#include <windows.h>
#else
#include <signal.h>
#include <sys/time.h>
#endif

#include <cerrno>
#include <cstring>

#include "signal_handlers.h"

namespace CVC4 {
namespace main {

#if defined(__MINGW32__) || defined(__MINGW64__)
void CALLBACK win_timeout_handler(LPVOID lpArg,
                                  DWORD dwTimerLowValue,
                                  DWORD dwTimerHighValue)
{
  signal_handlers::timeout_handler();
}
#else
void posix_timeout_handler(int sig, siginfo_t* info, void*)
{
  signal_handlers::timeout_handler();
}
#endif

void install_time_limit(const Options& opts)
{
  unsigned long ms = opts.getCumulativeTimeLimit();
  // Skip if no time limit shall be set.
  if (ms == 0) return;

#if defined(__MINGW32__) || defined(__MINGW64__)
  HANDLE hTimer = CreateWaitableTimer(nullptr, true, TEXT("CVC4::Timeout"));
  if (hTimer == nullptr)
  {
    throw Exception(std::string("CreateWaitableTimer() failure: ")
                    + std::to_string(GetLastError()));
  }
  LARGE_INTEGER liDueTime;
  liDueTime.LowPart = (DWORD)(ms & 0xFFFFFFFF);
  liDueTime.HighPart = 0;
  if (!SetWaitableTimer(
          hTimer, &liDueTime, 0, win_timeout_handler, nullptr, false))
  {
    throw Exception(std::string("SetWaitableTimer() failure: ")
                    + std::to_string(GetLastError()));
  }
#else
  // Install a signal handler for SIGALRM
  struct sigaction sact;
  sact.sa_sigaction = posix_timeout_handler;
  sact.sa_flags = SA_SIGINFO;
  sigemptyset(&sact.sa_mask);
  if (sigaction(SIGALRM, &sact, NULL))
  {
    throw Exception(std::string("sigaction(SIGALRM) failure: ")
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
    throw Exception(std::string("timer_settime() failure: ") + strerror(errno));
  }
#endif
}

}  // namespace main
}  // namespace CVC4
