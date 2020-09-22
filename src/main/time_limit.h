/*********************                                                        */
/*! \file time_limit.h
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

#ifndef CVC4__MAIN__TIME_LIMIT_H
#define CVC4__MAIN__TIME_LIMIT_H

#include "options/options.h"

namespace CVC4 {
namespace main {

/**
 * Installs an overall wall-clock time limit for the solver binary.
 * It retrieves the time limit and creates a POSIX timer (via setitimer()).
 * This timer signals its expiration with an SIGALRM that is handled by
 * timeout_handler() in signal_handler.cpp.
 * For windows, we use a timer (via SetWaitableTimer()) that uses
 * timeout_handler() as callback function.
 */
void install_time_limit(const Options& opts);

}  // namespace main
}  // namespace CVC4

#endif /* CVC4__MAIN__TIME_LIMIT_H */
