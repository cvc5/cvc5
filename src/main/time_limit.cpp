#include "time_limit.h"

#if defined(__MINGW32__) || defined(__MINGW64__)
#include <windows.h>

#include "signal_handlers.h"
#else
#include <sys/time.h>
#endif

#include <cerrno>
#include <cstring>

namespace CVC4 {
namespace main {

#if defined(__MINGW32__) || defined(__MINGW64__)
void CALLBACK win_timeout_handler(LPVOID lpArg,
                                  DWORD dwTimerLowValue,
                                  DWORD dwTimerHighValue)

{
  signal_handlers::timeout_handler();
}
#endif

void install_time_limit(const Options& opts)
{
  unsigned long ms = opts.getCumulativeTimeLimit();
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
  // Check https://linux.die.net/man/2/setitimer
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
