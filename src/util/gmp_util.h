/*
 * gmp.h
 *
 *  Created on: Apr 5, 2010
 *      Author: dejan
 */

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
