/*********************                                                        */
/*! \file strings_process_loop_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Modes for processing looping word equations in the string solver.
 **
 ** Modes for processing looping word equations in the string solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__PROCESS_LOOP_MODE_H
#define __CVC4__THEORY__STRINGS__PROCESS_LOOP_MODE_H

#include <iosfwd>

namespace CVC4 {
namespace theory {
namespace strings {

/** Enumeration of bit-blasting modes */
enum class ProcessLoopMode
{
  /** Perform full loop processing. */
  FULL,

  /** Omit normal loop breaking. */
  SIMPLE,

  /** Abort if normal loop breaking is required. */
  SIMPLE_ABORT,

  /** Omit loop processing. */
  NONE,

  /** Abort if looping word equations are encountered. */
  ABORT
}; // enum ProcessLoopMode

}  // namespace strings
}  // namespace theory

std::ostream& operator<<(std::ostream& out,
                         theory::strings::ProcessLoopMode mode);

}  // namespace CVC4

#endif /* __CVC4__THEORY__BV__BITBLAST_MODE_H */
