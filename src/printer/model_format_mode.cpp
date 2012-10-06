/*********************                                                        */
/*! \file model_format_mode.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
