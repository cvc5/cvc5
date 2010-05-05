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

  BitVector(const std::string& num, unsigned base = 2)
  : d_size(1), d_value(0) {}

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

  unsigned getSize() const {
    return d_size;
  }
};

/**
 * Hash function for the BitVector constants.
 */
struct BitVectorHashStrategy {
  static inline size_t hash(const BitVector& bv) {
    return bv.hash();
  }
};

/**
 * The structure representing the extraction operation for bit-vectors. The
 * operation map bit-vectors to bit-vector of size <code>high - low + 1</code>
 * by taking the bits at indices <code>high ... low</code>
 */
struct BitVectorExtract  {
  /** The high bit of the range for this extract */
  unsigned high;
  /** The low bit of the range for this extract */
  unsigned low;

  BitVectorExtract(unsigned high, unsigned low)
  : high(high), low(low) {}

  bool operator == (const BitVectorExtract& extract) const {
    return high == extract.high && low == extract.low;
  }
};

/**
 * Hash function for the BitVectorExtract objects.
 */
class BitVectorExtractHashStrategy {
public:
  static size_t hash(const BitVectorExtract& extract) {
    size_t hash = extract.low;
    hash ^= extract.high + 0x9e3779b9 + (hash << 6) + (hash >> 2);
    return hash;
  }
};

struct BitVectorSize {
  unsigned size;
  BitVectorSize(unsigned size)
  : size(size) {}
  operator unsigned () const { return size; }
};

struct BitVectorRepeat {
  unsigned repeatAmount;
  BitVectorRepeat(unsigned repeatAmount)
  : repeatAmount(repeatAmount) {}
  operator unsigned () const { return repeatAmount; }
};

struct BitVectorZeroExtend {
  unsigned zeroExtendAmount;
  BitVectorZeroExtend(unsigned zeroExtendAmount)
  : zeroExtendAmount(zeroExtendAmount) {}
  operator unsigned () const { return zeroExtendAmount; }
};

struct BitVectorSignExtend {
  unsigned signExtendAmount;
  BitVectorSignExtend(unsigned signExtendAmount)
  : signExtendAmount(signExtendAmount) {}
  operator unsigned () const { return signExtendAmount; }
};

struct BitVectorRotateLeft {
  unsigned rotateLeftAmount;
  BitVectorRotateLeft(unsigned rotateLeftAmount)
  : rotateLeftAmount(rotateLeftAmount) {}
  operator unsigned () const { return rotateLeftAmount; }
};

struct BitVectorRotateRight {
  unsigned rotateRightAmount;
  BitVectorRotateRight(unsigned rotateRightAmount)
  : rotateRightAmount(rotateRightAmount) {}
  operator unsigned () const { return rotateRightAmount; }
};

template <typename T>
struct UnsignedHashStrategy {
  static inline size_t hash(const T& x) {
    return (size_t)x;
  }
};

std::ostream& operator <<(std::ostream& os, const BitVector& bv);
std::ostream& operator <<(std::ostream& os, const BitVectorExtract& bv);
}


#endif /* __CVC4__BITVECTOR_H_ */
