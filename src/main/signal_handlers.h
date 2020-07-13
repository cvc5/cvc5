/*********************                                                        */
/*! \file signal_handlers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of signal handlers.
 **
 ** Implementation of signal handlers.
 **/

#ifndef CVC4__MAIN__SIGNAL_HANDLERS_H
#define CVC4__MAIN__SIGNAL_HANDLERS_H

namespace CVC4 {
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
 * Also sets callbacks via std::set_unexpected and std:set_terminate.
 */
void install();

/**
 * Performs cleanup related to the signal handlers.
 */
void cleanup();

}  // namespace signal_handlers
}  // namespace main
}  // namespace CVC4

#endif /* CVC4__MAIN__SIGNAL_HANDLERS_H */
