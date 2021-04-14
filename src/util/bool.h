/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A hash function for Boolean.
 */

#include "cvc5_public.h"

#ifndef CVC5__BOOL_H
#define CVC5__BOOL_H

namespace cvc5 {

struct BoolHashFunction {
  inline size_t operator()(bool b) const {
    return b;
  }
};/* struct BoolHashFunction */

}  // namespace cvc5

#endif /* CVC5__BOOL_H */
