/*********************                                                        */
/*! \file bitvector.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway
 ** Minor contributors (to current version): mdeters
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

#include "cvc4_public.h"

#ifndef __CVC4__BITVECTOR_H_
#define __CVC4__BITVECTOR_H_

#include <iostream>
#include "util/Assert.h"
#include "util/gmp_util.h"
#include "util/integer.h"

namespace CVC4 {

class BitVector {

private:

  unsigned d_size;
  Integer d_value;

  BitVector(unsigned size, const Integer& val) : d_size(size), d_value(val) {}

public:

  BitVector(unsigned size = 0)
  : d_size(size), d_value(0) {}

  BitVector(unsigned size, unsigned int z)
  : d_size(size), d_value(z) {}

  BitVector(unsigned size, unsigned long int z)
  : d_size(size), d_value(z) {}

  BitVector(unsigned size, const BitVector& q)
  : d_size(size), d_value(q.d_value) {}

  BitVector(const std::string& num, unsigned base = 2);

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
    return d_value.hash();
  }

  std::string toString(unsigned int base = 2) const {
    std::string str = d_value.toString(base);
    if( base == 2 && d_size > str.size() ) {
      std::string zeroes;
      for( unsigned int i=0; i < d_size - str.size(); ++i ) {
        zeroes.append("0");
      }
      return zeroes + str;
    } else {
      return str;
    }
  }

  unsigned getSize() const {
    return d_size;
  }
};

inline BitVector::BitVector(const std::string& num, unsigned base) {
  AlwaysAssert( base == 2 || base == 16 );

  if( base == 2 ) {
    d_size = num.size();
//    d_value = Integer(num,2);
/*
    for( string::const_iterator it = num.begin(); it != num.end(); ++it ) {
      if( *it != '0' || *it != '1' ) {
        IllegalArgument(num, "BitVector argument is not a binary string.");
      }
      z = (Integer(2) * z) + (*it == '1');
      d_value = mpz_class(z.get_mpz());
    }
*/
  } else if( base == 16 ) {
    d_size = num.size() * 4;
//    // Use a stream to decode the hex string
//    stringstream ss;
//    ss.setf(ios::hex, ios::basefield);
//    ss << num;
//    ss >> z;
//    d_value = mpz_class(z);
//    break;
  } else {
    Unreachable("Unsupported base in BitVector(std::string&, unsigned int).");
  }

  d_value = Integer(num,base);
}


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
