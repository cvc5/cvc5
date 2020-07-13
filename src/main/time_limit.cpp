#include "time_limit.h"

#include <sys/time.h>

#include <cerrno>
#include <cstring>

namespace CVC4 {
namespace main {

void install_time_limit(const Options& opts)
{
  unsigned long ms = opts.getCumulativeTimeLimit();
  if (ms == 0) return;

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
}

}  // namespace main
}  // namespace CVC4
