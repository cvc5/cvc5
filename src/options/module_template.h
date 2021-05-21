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

#ifndef CVC5__OPTIONS__${id_cap}$_H
#define CVC5__OPTIONS__${id_cap}$_H

#include "options/options.h"

// clang-format off
${includes}$
// clang-format on

namespace cvc5 {
namespace options {

// clang-format off
${modes}$
// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct Holder${id_cap}$
{
// clang-format off
${holder_spec}$
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

// clang-format off
${decls}$
// clang-format on

namespace ${id}$
{
// clang-format off
${option_names}$
// clang-format on
}

}  // namespace options

// clang-format off
${specs}$
// clang-format on

namespace options {
// clang-format off
${inls}$
// clang-format on

}  // namespace options
}  // namespace cvc5

#endif /* CVC5__OPTIONS__${id_cap}$_H */
