/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Contains code for handling command-line options.
 *
 * For each <module>_options.toml configuration file, mkoptions.py
 * expands this template and generates a <module>_options.h file.
 */

#include "cvc5_private.h"

#ifndef CVC5__OPTIONS__${id}$_H
#define CVC5__OPTIONS__${id}$_H

#include "options/options.h"

// clang-format off
${includes}$

${holder_spec}$

namespace cvc5 {
namespace options {

${modes}$

${decls}$

}  // namespace options

${specs}$

namespace options {
${inls}$

}  // namespace options
}  // namespace cvc5

#endif /* CVC5__OPTIONS__${id}$_H */
//clang-format on
