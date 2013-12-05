/*********************                                                        */
/*! \file gmp_util.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__GMP_UTIL_H
#define __CVC4__GMP_UTIL_H

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

#endif /* __CVC4__GMP_UTIL_H */
