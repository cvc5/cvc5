/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "cvc4_private.h"

#ifndef CVC5__OPTIONS__OPTIONS_HOLDER_H
#define CVC5__OPTIONS__OPTIONS_HOLDER_H

// clang-format off
${headers_module}$

namespace cvc5 {
namespace options {

struct OptionsHolder
{
  OptionsHolder();
  ${macros_module}$

}; /* struct OptionsHolder */

}  // namespace options
}  // namespace cvc5

#endif /* CVC5__OPTIONS__OPTIONS_HOLDER_H */
// clang-format on
