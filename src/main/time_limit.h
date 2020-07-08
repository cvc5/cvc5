#ifndef CVC4__MAIN__TIME_LIMIT_H
#define CVC4__MAIN__TIME_LIMIT_H

#include <time.h>

#include "base/listener.h"
#include "options/options.h"

namespace CVC4 {
namespace main {

/** Manages an overall wall-clock time limit for the solver binary.
 * It works as a listener to an Options object.
 * When notified, it retrieves the time limit and creates a POSIX timer (via
 * setitimer()). This timer signals its expiration with an SIGALRM that is
 * handled by timeout_handler() in util.cpp. Note that this class expects a
 * reference to an Options object, while other listeners don't, as the
 * OptionsScope is not yet initialized when we set up this timer.
 */
class TimeLimitListener : public CVC4::Listener
{
  /** A reference to the Options object. */
  const Options& options;

 public:
  /** Create a listener with the given Options object. */
  TimeLimitListener(const Options& opts) : options(opts) {}
  /** Retrieves timeout from Options and creates a timer. */
  void notify() override;
};

}  // namespace main
}  // namespace CVC4

#endif /* CVC4__MAIN__TIME_LIMIT_H */
