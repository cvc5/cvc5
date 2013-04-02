/*********************                                                        */
/*! \file model_format_mode.h
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

#include "cvc4_public.h"

#ifndef __CVC4__PRINTER__MODEL_FORMAT_MODE_H
#define __CVC4__PRINTER__MODEL_FORMAT_MODE_H

#include <iostream>

namespace CVC4 {

/** Enumeration of model_format modes (how to print models from get-model command). */
typedef enum {
  /** default mode (print expressions in the output language format) */
  MODEL_FORMAT_MODE_DEFAULT,
  /** print functional values in a table format */
  MODEL_FORMAT_MODE_TABLE,
} ModelFormatMode;

std::ostream& operator<<(std::ostream& out, ModelFormatMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__MODEL_FORMAT_H */
