/*********************                                                        */
/*! \file strings_modes.cpp
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

#include "options/strings_modes.h"

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

std::ostream& operator<<(std::ostream& out,
                         theory::strings::RegExpInterMode mode)
{
  switch (mode)
  {
    case theory::strings::RegExpInterMode::RE_INTER_ALL:
      out << "RegExpInterMode::RE_INTER_ALL";
      break;
    case theory::strings::RegExpInterMode::RE_INTER_CONSTANT:
      out << "RegExpInterMode::RE_INTER_CONSTANT";
      break;
    case theory::strings::RegExpInterMode::RE_INTER_ONE_CONSTANT:
      out << "RegExpInterMode::RE_INTER_ONE_CONSTANT";
      break;
    case theory::strings::RegExpInterMode::RE_INTER_NONE:
      out << "RegExpInterMode::RE_INTER_NONE";
      break;
    default:
      out << "RegExpInterMode:UNKNOWN![" << static_cast<int64_t>(mode) << "]";
  }
  return out;
}

}  // namespace CVC4
