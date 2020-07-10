#ifndef CVC4__MAIN__TIME_LIMIT_H
#define CVC4__MAIN__TIME_LIMIT_H

#include "options/options.h"

namespace CVC4 {
namespace main {

/**
 * Installs an overall wall-clock time limit for the solver binary.
 * It retrieves the time limit and creates a POSIX timer (via setitimer()).
 * This timer signals its expiration with an SIGALRM that is handled by
 * timeout_handler() in util.cpp.
 */

void install_time_limit(const Options& opts);

}  // namespace main
}  // namespace CVC4

#endif /* CVC4__MAIN__TIME_LIMIT_H */
