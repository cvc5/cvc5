/*********************                                                        */
/*! \file strings_modes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Modes for the string solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__STRINGS_MODES_H
#define CVC4__THEORY__STRINGS__STRINGS_MODES_H

#include <iosfwd>

namespace CVC4 {
namespace theory {
namespace strings {

/** Enumeration of string processing loop modes */
enum ProcessLoopMode
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
};  // enum ProcessLoopMode

/** Enumeration of regular expression intersection modes */
enum RegExpInterMode
{
  /** Compute intersections for all regular expressions. */
  RE_INTER_ALL,

  /**
   * Compute intersections only for regular expressions without re.allchar
   * and re.range.
   */
  RE_INTER_CONSTANT,

  /**
   * Compute intersections only between regular expressions where one side does
   * not contain re.allchar and re.range.
   */
  RE_INTER_ONE_CONSTANT,

  /** Do not compute intersections of regular expressions. */
  RE_INTER_NONE,
};  // enum RegExpInterMode

}  // namespace strings
}  // namespace theory

std::ostream& operator<<(std::ostream& out,
                         theory::strings::ProcessLoopMode mode);

std::ostream& operator<<(std::ostream& out,
                         theory::strings::RegExpInterMode mode);

}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRINGS_MODES_H */
