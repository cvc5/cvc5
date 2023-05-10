/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
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
 */

#ifndef CVC5__MAIN__TIME_LIMIT_H
#define CVC5__MAIN__TIME_LIMIT_H

#include <cstdint>

namespace cvc5::main {

/**
 * This class makes sure that the main thread signals back to the time
 * limit mechanism when it wants to terminate. This is necessary if we
 * use our custom std::thread-based timers. Following RAII, we signal
 * this using a destructor so that we can never forget to abort the time
 * limit thread.
 */
struct TimeLimit
{
    ~TimeLimit();
};

/**
 * Installs an overall wall-clock time limit for the solver binary.
 * It retrieves the time limit and creates a POSIX timer (via setitimer()).
 * This timer signals its expiration with an SIGALRM that is handled by
 * timeout_handler() in signal_handler.cpp.
 * If the POSIX timers are not available (e.g., we are running on windows)
 * we implement our own timer based on std::thread. In this case, the main
 * thread needs to communicate back to the timer thread when it wants to
 * terminate, which is done via the TimeLimit object.
 */
TimeLimit install_time_limit(uint64_t ms);

}  // namespace cvc5::main

#endif /* CVC5__MAIN__TIME_LIMIT_H */
