/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

// clang-format off
#ifndef CVC5__OPTIONS__${id_cap}$_H
#define CVC5__OPTIONS__${id_cap}$_H

#include "options/options.h"

${includes}$

namespace cvc5::internal::options {

namespace ${id}$::longName {
  ${long_name_decl}$
}

${modes_decl}$
  // clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

      // clang-format off
struct Holder${id_cap}$
{
  ${holder_decl}$
};
  // clang-format on

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__${id_cap}$_H */
