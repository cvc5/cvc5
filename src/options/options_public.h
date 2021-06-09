/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Public facing functions for options that need to be accessed from the
 * outside.
 *
 * These are all one line wrappers for accessing the internal option data so
 * that external code (including parser/ and main/) does not need to include
 * the option modules (*_options.h).
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_PUBLIC_H
#define CVC5__OPTIONS__OPTIONS_PUBLIC_H

#include "options/options.h"

namespace cvc5::options {

bool getUfHo(const Options& opts) CVC5_EXPORT;

}  // namespace cvc5::options

#endif
