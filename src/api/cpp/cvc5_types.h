/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common cvc5 types.
 */

#include "cvc5_export.h"

#ifndef CVC5__API__CVC5_TYPES_H
#define CVC5__API__CVC5_TYPES_H

namespace cvc5::modes {

enum BlockModelsMode
{
  /** Block models based on the SAT skeleton. */
  LITERALS,
  /** Block models based on the concrete model values for the free variables. */
  VALUES
};

}

#endif
