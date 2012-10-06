/*********************                                                        */
/*! \file model_format_mode.h
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
