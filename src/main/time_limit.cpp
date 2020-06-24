#include "time_limit.h"

#include <signal.h>
#include <time.h>

#include <cerrno>
#include <cstring>

namespace CVC4 {
namespace main {

TimeLimitListener::~TimeLimitListener()
{
  if (timerid != 0)
  {
    timer_delete(timerid);
  }
}

void TimeLimitListener::notify()
{
  unsigned long ms = options.getCumulativeTimeLimit();

  // Check https://linux.die.net/man/7/sigevent
  // Notify by SIGXCPU
  struct sigevent sev;
  sev.sigev_notify = SIGEV_SIGNAL;
  sev.sigev_signo = SIGXCPU;

  // Check https://linux.die.net/man/2/timer_create
  if (timer_create(CLOCK_MONOTONIC, &sev, &timerid))
  {
    throw Exception(std::string("timer_create() failure: ") + strerror(errno));
  }

  // Check https://linux.die.net/man/2/timer_settime
  struct itimerspec timerspec;
  timerspec.it_value.tv_sec = ms / 1000;
  timerspec.it_value.tv_nsec = (ms % 1000) * 1000000;
  timerspec.it_interval.tv_sec = 0;
  timerspec.it_interval.tv_nsec = 0;
  // Argument 1: the timer id
  // Argument 2: flags, we don't need any
  // Argument 3: timer configuration, relative to current time
  // Argument 4: old timer configuration, we don't want to know
  if (timer_settime(timerid, 0, &timerspec, nullptr))
  {
    throw Exception(std::string("timer_settime() failure: ") + strerror(errno));
  }
}

}  // namespace main
}  // namespace CVC4
