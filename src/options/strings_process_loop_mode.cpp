/*********************                                                        */
/*! \file strings_process_loop_mode.cpp
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

#include "options/strings_process_loop_mode.h"

#include <cstdint>
#include <iostream>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out,
                         theory::strings::ProcessLoopMode mode)
{
  switch (mode)
  {
    case theory::strings::ProcessLoopMode::FULL:
      out << "ProcessLoopMode::FULL";
      break;
    case theory::strings::ProcessLoopMode::SIMPLE:
      out << "ProcessLoopMode::SIMPLE";
      break;
    case theory::strings::ProcessLoopMode::SIMPLE_ABORT:
      out << "ProcessLoopMode::SIMPLE_ABORT";
      break;
    case theory::strings::ProcessLoopMode::NONE:
      out << "ProcessLoopMode::NONE";
      break;
    case theory::strings::ProcessLoopMode::ABORT:
      out << "ProcessLoopMode::ABORT";
      break;
    default:
      out << "ProcessLoopMode:UNKNOWN![" << static_cast<int64_t>(mode) << "]";
  }
  return out;
}

}  // namespace CVC4
