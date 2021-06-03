/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of signal handlers.
 */

#ifndef CVC5__MAIN__SIGNAL_HANDLERS_H
#define CVC5__MAIN__SIGNAL_HANDLERS_H

namespace cvc5 {
namespace main {
namespace signal_handlers {

/**
 * Performs last steps before termination due to a timeout.
 * Prints an appropriate message and solver statistics.
 */
void timeout_handler();

/**
 * Installs (almost) all signal handlers.
 * A handler for SIGALRM is set in time_limit.cpp.
 * Also sets callbacks via std:set_terminate.
 */
void install();

/**
 * Performs cleanup related to the signal handlers.
 */
void cleanup();

}  // namespace signal_handlers
}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__SIGNAL_HANDLERS_H */
