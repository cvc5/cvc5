/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Standardized type for efficient array indexing.
 */

#include "util/index.h"

#include <limits>

namespace cvc5 {

static_assert(sizeof(Index) <= sizeof(size_t),
              "Index cannot be larger than size_t");
static_assert(!std::numeric_limits<Index>::is_signed,
              "Index must be unsigned");

/* Discussion: Why is Index a uint32_t instead of size_t (or uint_fast32_t)?
 *
 * size_t is a more appropriate choice than uint32_t as the choice is dictated
 * by uniqueness in arrays and vectors. These correspond to size_t. However, the
 * using size_t with a sizeof == 8 on 64 bit platforms is noticeably slower.
 * (Limited testing suggests a ~1/16 of running time.) Interestingly,
 * uint_fast32_t also has a sizeof == 8 on x86_64.
 */
}  // namespace cvc5
