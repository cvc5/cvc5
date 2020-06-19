/*********************                                                        */
/*! \file printer_modes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "options/printer_modes.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, options::InstFormatMode mode)
{
  out << "InstFormatMode::";
  switch (mode)
  {
    case options::InstFormatMode::DEFAULT: out << "DEFAULT"; break;
    case options::InstFormatMode::SZS: out << "SZS"; break;
    default: out << "UNKNOWN![" << unsigned(mode) << "]";
  }
  return out;
}

}  // namespace CVC4
