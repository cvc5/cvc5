/*********************                                                        */
/*! \file model_format_mode.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "printer/model_format_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, ModelFormatMode mode) {
  switch(mode) {
  case MODEL_FORMAT_MODE_DEFAULT:
    out << "MODEL_FORMAT_MODE_DEFAULT";
    break;
  case MODEL_FORMAT_MODE_TABLE:
    out << "MODEL_FORMAT_MODE_TABLE";
    break;
  default:
    out << "ModelFormatMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

}/* CVC4 namespace */
