/*********************                                                        */
/*! \file gmp_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef CVC4__GMP_UTIL_H
#define CVC4__GMP_UTIL_H

/*
 * Older versions of GMP in combination with newer versions of GCC and C++11
 * cause errors: https://gcc.gnu.org/gcc-4.9/porting_to.html
 * Including <cstddef> is a workaround for this issue.
 */
#include <cstddef>

#include <gmpxx.h>

namespace CVC4 {

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

}/* CVC4 namespace */

#endif /* CVC4__GMP_UTIL_H */
