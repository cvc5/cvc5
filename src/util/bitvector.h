/*
 * bitvector.h
 *
 *  Created on: Mar 31, 2010
 *      Author: dejan
 */

#ifndef __CVC4__BITVECTOR_H_
#define __CVC4__BITVECTOR_H_

#include <string>
#include <iostream>
#include "util/gmp_util.h"

namespace CVC4 {

class BitVector {

private:

  unsigned d_size;
  mpz_class d_value;

  BitVector(unsigned size, const mpz_class& val) : d_size(size), d_value(val) {}

public:

  BitVector(unsigned size = 0)
  : d_size(size), d_value(0) {}

  BitVector(unsigned size, unsigned int z)
  : d_size(size), d_value(z) {}

  BitVector(unsigned size, unsigned long int z)
  : d_size(size), d_value(z) {}

  BitVector(unsigned size, const BitVector& q)
  : d_size(size), d_value(q.d_value) {}

  ~BitVector() {}

  BitVector& operator =(const BitVector& x) {
    if(this == &x)
      return *this;
    d_value = x.d_value;
    return *this;
  }

  bool operator ==(const BitVector& y) const {
    if (d_size != y.d_size) return false;
    return d_value == y.d_value;
  }

  bool operator !=(const BitVector& y) const {
    if (d_size == y.d_size) return false;
    return d_value != y.d_value;
  }

  BitVector operator +(const BitVector& y) const {
    return BitVector(std::max(d_size, y.d_size), d_value + y.d_value);
  }

  BitVector operator -(const BitVector& y) const {
    return *this + ~y + 1;
  }

  BitVector operator -() const {
    return ~(*this) + 1;
  }

  BitVector operator *(const BitVector& y) const {
    return BitVector(d_size, d_value * y.d_value);
  }

  BitVector operator ~() const {
    return BitVector(d_size, d_value);
  }

  size_t hash() const {
    return gmpz_hash(d_value.get_mpz_t());
  }

  std::string toString(unsigned int base = 2) const {
    return d_value.get_str(base);
  }
};

struct BitVectorHashStrategy {
  static inline size_t hash(const BitVector& bv) {
    return bv.hash();
  }
};

std::ostream& operator <<(std::ostream& os, const BitVector& bv);

}


#endif /* __CVC4__BITVECTOR_H_ */
