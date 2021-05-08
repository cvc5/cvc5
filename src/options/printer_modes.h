/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_public.h"

#ifndef CVC5__PRINTER__MODES_H
#define CVC5__PRINTER__MODES_H

#include <iostream>

namespace cvc5 {
namespace options {

/** Enumeration of inst_format modes (how to print models from get-model
 * command). */
enum class InstFormatMode
{
  /** default mode (print expressions in the output language format) */
  DEFAULT,
  /** print as SZS proof */
  SZS,
};

}  // namespace options

std::ostream& operator<<(std::ostream& out, options::InstFormatMode mode);

}  // namespace cvc5

#endif /* CVC5__PRINTER__MODEL_FORMAT_H */
