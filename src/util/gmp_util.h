/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner, Morgan Deters
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

#ifndef CVC5__GMP_UTIL_H
#define CVC5__GMP_UTIL_H

#include <gmpxx.h>

namespace cvc5 {

/** Hashes the gmp integer primitive in a word by word fashion. */
inline size_t gmpz_hash(const mpz_t toHash) {
  size_t hash = 0;
  for (int i = 0, n = mpz_size(toHash); i < n; ++i){
    mp_limb_t limb = mpz_getlimbn(toHash, i);
    hash = hash * 2;
    hash = hash xor limb;
  }
  return hash;
}/* gmpz_hash() */

}  // namespace cvc5

#endif /* CVC5__GMP_UTIL_H */
