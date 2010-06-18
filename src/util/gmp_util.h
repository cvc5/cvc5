/*********************                                                        */
/*! \file gmp_util.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#ifndef __CVC4__GMP_H_
#define __CVC4__GMP_H_

#include <gmpxx.h>

namespace CVC4 {

  /** Hashes the gmp integer primitive in a word by word fashion. */
  inline size_t gmpz_hash(const mpz_t toHash) {
    size_t hash = 0;
    for (int i=0, n=mpz_size(toHash); i<n; ++i){
      mp_limb_t limb = mpz_getlimbn(toHash, i);
      hash = hash * 2;
      hash = hash xor limb;
    }
    return hash;
  }

}

#endif /* __CVC4__GMP_H_ */
