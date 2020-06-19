/*********************                                                        */
/*! \file printer_modes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andrew Reynolds, Tim King
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

#include "cvc4_public.h"

#ifndef CVC4__PRINTER__MODES_H
#define CVC4__PRINTER__MODES_H

#include <iostream>

namespace CVC4 {
namespace options {

/** Enumeration of inst_format modes (how to print models from get-model
 * command). */
enum class CVC4_PUBLIC InstFormatMode
{
  /** default mode (print expressions in the output language format) */
  DEFAULT,
  /** print as SZS proof */
  SZS,
};

}  // namespace options

std::ostream& operator<<(std::ostream& out,
                         options::InstFormatMode mode) CVC4_PUBLIC;

}  // namespace CVC4

#endif /* CVC4__PRINTER__MODEL_FORMAT_H */
