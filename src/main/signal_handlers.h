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

void timeout_handler();

void install();
void cleanup();

}  // namespace signal_handlers
}  // namespace main
}  // namespace CVC4

#endif /* CVC4__MAIN__SIGNAL_HANDLERS_H */
