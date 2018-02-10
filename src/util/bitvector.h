/*********************                                                        */
/*! \file bitvector.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Liana Hadarean, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A fixed-size bit-vector.
 **
 ** A fixed-size bit-vector, implemented as a wrapper around Integer.
 **
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BITVECTOR_H
#define __CVC4__BITVECTOR_H

#include <iosfwd>

#include "base/exception.h"
#include "util/integer.h"

namespace CVC4 {

class CVC4_PUBLIC BitVector {
public:

  BitVector(unsigned size, const Integer& val):
    d_size(size),
    d_value(val.modByPow2(size))
      {}

  BitVector(unsigned size = 0)
    : d_size(size), d_value(0) {}

  BitVector(unsigned size, unsigned int z)
    : d_size(size), d_value(z) {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, unsigned long int z)
    : d_size(size), d_value(z) {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, const BitVector& q)
    : d_size(size), d_value(q.d_value) {}

  BitVector(const std::string& num, unsigned base = 2)
  {
    CheckArgument(base == 2 || base == 16, base);
    d_size = base == 2 ?  num.size() : num.size() * 4;
    d_value = Integer(num, base);
  }

  ~BitVector() {}

  BitVector& operator=(const BitVector& x)
  {
    if (this == &x) return *this;
    d_size = x.d_size;
    d_value = x.d_value;
    return *this;
  }

  unsigned getSize() const
  {
    return d_size;
  }

  const Integer& getValue() const
  {
    return d_value;
  }

  Integer toInteger() const
  {
    return d_value;
  }

  /**
   * Return Integer corresponding to two's complement interpretation of bv.
   */
  Integer toSignedInteger() const
  {
    unsigned size = d_size;
    Integer sign_bit = d_value.extractBitRange(1, size - 1);
    Integer val = d_value.extractBitRange(size - 1, 0);
    Integer res = Integer(-1) * sign_bit.multiplyByPow2(size - 1) + val;
    return res;
  }

  size_t hash() const
  {
    return d_value.hash() + d_size;
  }

  std::string toString(unsigned int base = 2) const
  {
    std::string str = d_value.toString(base);
    if (base == 2 && d_size > str.size())
    {
      std::string zeroes;
      for (unsigned int i = 0; i < d_size - str.size(); ++i)
      {
        zeroes.append("0");
      }
      return zeroes + str;
    }
    else
    {
      return str;
    }
  }

  BitVector setBit(uint32_t i) const
  {
    CheckArgument(i < d_size, i);
    Integer res = d_value.setBit(i);
    return BitVector(d_size, res);
  }

  bool isBitSet(uint32_t i) const
  {
    CheckArgument(i < d_size, i);
    return d_value.isBitSet(i);
  }


  /**
   * Return k if the integer is equal to 2^{k-1} and zero otherwise.
   */
  unsigned isPow2() {
    return d_value.isPow2();
  }

  /* -----------------------------------------------------------------------
   ** Operators
   * ----------------------------------------------------------------------- */

  /* String Operations ----------------------------------------------------- */

  BitVector concat (const BitVector& other) const {
    return BitVector(d_size + other.d_size, (d_value.multiplyByPow2(other.d_size)) + other.d_value);
  }

  BitVector extract(unsigned high, unsigned low) const {
    return BitVector(high - low + 1, d_value.extractBitRange(high - low + 1, low));
  }

  /* (Dis)Equality --------------------------------------------------------- */

  bool operator ==(const BitVector& y) const {
    if (d_size != y.d_size) return false;
    return d_value == y.d_value;
  }

  bool operator !=(const BitVector& y) const {
    if (d_size != y.d_size) return true;
    return d_value != y.d_value;
  }

  /* Unsigned Inequality --------------------------------------------------- */

  bool operator <(const BitVector& y) const {
    return d_value < y.d_value;
  }

  bool unsignedLessThan(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    CheckArgument(d_value >= 0, this);
    CheckArgument(y.d_value >= 0, y);
    return d_value < y.d_value;
  }

  bool operator <=(const BitVector& y) const {
    return d_value <= y.d_value;
  }

  bool unsignedLessThanEq(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, this);
    CheckArgument(d_value >= 0, this);
    CheckArgument(y.d_value >= 0, y);
    return d_value <= y.d_value;
  }

  bool operator >(const BitVector& y) const {
    return d_value > y.d_value ;
  }

  bool operator >=(const BitVector& y) const {
    return d_value >= y.d_value ;
  }

  /* Signed Inequality ----------------------------------------------------- */

  bool signedLessThan(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    CheckArgument(d_value >= 0, this);
    CheckArgument(y.d_value >= 0, y);
    Integer a = (*this).toSignedInteger();
    Integer b = y.toSignedInteger();

    return a < b;
  }

  bool signedLessThanEq(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    CheckArgument(d_value >= 0, this);
    CheckArgument(y.d_value >= 0, y);
    Integer a = (*this).toSignedInteger();
    Integer b = y.toSignedInteger();

    return a <= b;
  }

  /* Bit-wise operations --------------------------------------------------- */

  /** xor */
  BitVector operator ^(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    return BitVector(d_size, d_value.bitwiseXor(y.d_value));
  }

  /** or */
  BitVector operator |(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    return BitVector(d_size, d_value.bitwiseOr(y.d_value));
  }

  /** and */
  BitVector operator &(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    return BitVector(d_size, d_value.bitwiseAnd(y.d_value));
  }

  /** not */
  BitVector operator ~() const {
    return BitVector(d_size, d_value.bitwiseNot());
  }


  /* Arithmetic operations ------------------------------------------------- */

  BitVector operator +(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    Integer sum = d_value +  y.d_value;
    return BitVector(d_size, sum);
  }

  BitVector operator -(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    // to maintain the invariant that we are only adding BitVectors of the
    // same size
    BitVector one(d_size, Integer(1));
    return *this + ~y + one;
  }

  BitVector operator -() const {
    BitVector one(d_size, Integer(1));
    return ~(*this) + one;
  }

  BitVector operator *(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    Integer prod = d_value * y.d_value;
    return BitVector(d_size, prod);
  }

  /**
   * Total division function.
   * Returns 2^d_size-1 (signed: -1) when the denominator is zero
   * (d_value / 0 = 2^d_size - 1).
   */
  BitVector unsignedDivTotal (const BitVector& y) const {

    CheckArgument(d_size == y.d_size, y);
    if (y.d_value == 0) {
      // under division by zero return -1
      return BitVector(d_size, Integer(1).oneExtend(1, d_size - 1));
    }
    CheckArgument(d_value >= 0, this);
    CheckArgument(y.d_value > 0, y);
    return BitVector(d_size, d_value.floorDivideQuotient(y.d_value));
  }

  /**
   * Total remainder function.
   * Returns d_value when the denominator is zero (d_value % 0 = d_value).
   */
  BitVector unsignedRemTotal(const BitVector& y) const {
    CheckArgument(d_size == y.d_size, y);
    if (y.d_value == 0) {
      return BitVector(d_size, d_value);
    }
    CheckArgument(d_value >= 0, this);
    CheckArgument(y.d_value > 0, y);
    return BitVector(d_size, d_value.floorDivideRemainder(y.d_value));
  }


  /* Extend operations ----------------------------------------------------- */

  BitVector zeroExtend(unsigned amount) const {
    return BitVector(d_size + amount, d_value);
  }

  BitVector signExtend(unsigned amount) const {
    Integer sign_bit = d_value.extractBitRange(1, d_size -1);
    if(sign_bit == Integer(0)) {
      return BitVector(d_size + amount, d_value);
    } else {
      Integer val = d_value.oneExtend(d_size, amount);
      return BitVector(d_size+ amount, val);
    }
  }

  /* Shift operations ------------------------------------------------------ */

  BitVector leftShift(const BitVector& y) const {
    if (y.d_value > Integer(d_size)) {
      return BitVector(d_size, Integer(0));
    }
    if (y.d_value == 0) {
      return *this;
    }
    // making sure we don't lose information casting
    CheckArgument(y.d_value < Integer(1).multiplyByPow2(32), y);
    uint32_t amount = y.d_value.toUnsignedInt();
    Integer res = d_value.multiplyByPow2(amount);
    return BitVector(d_size, res);
  }

  BitVector logicalRightShift(const BitVector& y) const {
    if(y.d_value > Integer(d_size)) {
      return BitVector(d_size, Integer(0));
    }
    // making sure we don't lose information casting
    CheckArgument(y.d_value < Integer(1).multiplyByPow2(32), y);
    uint32_t amount = y.d_value.toUnsignedInt();
    Integer res = d_value.divByPow2(amount);
    return BitVector(d_size, res);
  }

  BitVector arithRightShift(const BitVector& y) const {
    Integer sign_bit = d_value.extractBitRange(1, d_size - 1);
    if(y.d_value > Integer(d_size)) {
      if(sign_bit == Integer(0)) {
        return BitVector(d_size, Integer(0));
      } else {
        return BitVector(d_size, Integer(d_size).multiplyByPow2(d_size) -1 );
      }
    }

    if (y.d_value == 0) {
      return *this;
    }

    // making sure we don't lose information casting
    CheckArgument(y.d_value < Integer(1).multiplyByPow2(32), y);

    uint32_t amount  = y.d_value.toUnsignedInt();
    Integer rest = d_value.divByPow2(amount);

    if(sign_bit == Integer(0)) {
      return BitVector(d_size, rest);
    }
    Integer res = rest.oneExtend(d_size - amount, amount);
    return BitVector(d_size, res);
  }

  /* -----------------------------------------------------------------------
   ** Static helpers.
   * ----------------------------------------------------------------------- */

  /* Create bit-vector of ones of given size. */
  static BitVector mkOnes(unsigned size)
  {
    CheckArgument(size > 0, size);
    return BitVector(1, Integer(1)).signExtend(size - 1);
  }

  /* Create bit-vector representing the minimum signed value of given size. */
  static BitVector mkMinSigned(unsigned size)
  {
    CheckArgument(size > 0, size);
    return BitVector(size).setBit(size - 1);
  }

  /* Create bit-vector representing the maximum signed value of given size. */
  static BitVector mkMaxSigned(unsigned size)
  {
    CheckArgument(size > 0, size);
    return ~BitVector::mkMinSigned(size);
  }

 private:

  /**
   * Class invariants:
   *  - no overflows: 2^d_size < d_value
   *  - no negative numbers: d_value >= 0
   */

  unsigned d_size;
  Integer d_value;

};/* class BitVector */



/* -----------------------------------------------------------------------
 ** BitVector structs
 * ----------------------------------------------------------------------- */

/**
 * The structure representing the extraction operation for bit-vectors. The
 * operation maps bit-vectors to bit-vector of size <code>high - low + 1</code>
 * by taking the bits at indices <code>high ... low</code>
 */
struct CVC4_PUBLIC BitVectorExtract
{
  /** The high bit of the range for this extract */
  unsigned high;
  /** The low bit of the range for this extract */
  unsigned low;

  BitVectorExtract(unsigned high, unsigned low) : high(high), low(low) {}

  bool operator==(const BitVectorExtract& extract) const
  {
    return high == extract.high && low == extract.low;
  }
}; /* struct BitVectorExtract */

/**
 * The structure representing the extraction of one Boolean bit.
 */
struct CVC4_PUBLIC BitVectorBitOf {
  /** The index of the bit */
  unsigned bitIndex;
  BitVectorBitOf(unsigned i)
    : bitIndex(i) {}

  bool operator == (const BitVectorBitOf& other) const {
    return bitIndex == other.bitIndex;
  }
};/* struct BitVectorBitOf */

struct CVC4_PUBLIC BitVectorSize {
  unsigned size;
  BitVectorSize(unsigned size)
  : size(size) {}
  operator unsigned () const { return size; }
};/* struct BitVectorSize */

struct CVC4_PUBLIC BitVectorRepeat {
  unsigned repeatAmount;
  BitVectorRepeat(unsigned repeatAmount)
  : repeatAmount(repeatAmount) {}
  operator unsigned () const { return repeatAmount; }
};/* struct BitVectorRepeat */

struct CVC4_PUBLIC BitVectorZeroExtend {
  unsigned zeroExtendAmount;
  BitVectorZeroExtend(unsigned zeroExtendAmount)
  : zeroExtendAmount(zeroExtendAmount) {}
  operator unsigned () const { return zeroExtendAmount; }
};/* struct BitVectorZeroExtend */

struct CVC4_PUBLIC BitVectorSignExtend {
  unsigned signExtendAmount;
  BitVectorSignExtend(unsigned signExtendAmount)
  : signExtendAmount(signExtendAmount) {}
  operator unsigned () const { return signExtendAmount; }
};/* struct BitVectorSignExtend */

struct CVC4_PUBLIC BitVectorRotateLeft {
  unsigned rotateLeftAmount;
  BitVectorRotateLeft(unsigned rotateLeftAmount)
  : rotateLeftAmount(rotateLeftAmount) {}
  operator unsigned () const { return rotateLeftAmount; }
};/* struct BitVectorRotateLeft */

struct CVC4_PUBLIC BitVectorRotateRight {
  unsigned rotateRightAmount;
  BitVectorRotateRight(unsigned rotateRightAmount)
  : rotateRightAmount(rotateRightAmount) {}
  operator unsigned () const { return rotateRightAmount; }
};/* struct BitVectorRotateRight */

struct CVC4_PUBLIC IntToBitVector {
  unsigned size;
  IntToBitVector(unsigned size)
  : size(size) {}
  operator unsigned () const { return size; }
};/* struct IntToBitVector */


/* -----------------------------------------------------------------------
 ** Hash Function structs
 * ----------------------------------------------------------------------- */

/*
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC BitVectorHashFunction {
  inline size_t operator()(const BitVector& bv) const {
    return bv.hash();
  }
};/* struct BitVectorHashFunction */

/**
 * Hash function for the BitVectorExtract objects.
 */
struct CVC4_PUBLIC BitVectorExtractHashFunction {
  size_t operator()(const BitVectorExtract& extract) const {
    size_t hash = extract.low;
    hash ^= extract.high + 0x9e3779b9 + (hash << 6) + (hash >> 2);
    return hash;
  }
};/* struct BitVectorExtractHashFunction */

/**
 * Hash function for the BitVectorBitOf objects.
 */
struct CVC4_PUBLIC BitVectorBitOfHashFunction {
  size_t operator()(const BitVectorBitOf& b) const {
    return b.bitIndex;
  }
};/* struct BitVectorBitOfHashFunction */

template <typename T>
struct CVC4_PUBLIC UnsignedHashFunction {
  inline size_t operator()(const T& x) const {
    return (size_t)x;
  }
};/* struct UnsignedHashFunction */


/* -----------------------------------------------------------------------
 ** Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator <<(std::ostream& os, const BitVector& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const BitVector& bv) {
  return os << bv.toString();
}

inline std::ostream& operator <<(std::ostream& os, const BitVectorExtract& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const BitVectorExtract& bv) {
  return os << "[" << bv.high << ":" << bv.low << "]";
}

inline std::ostream& operator <<(std::ostream& os, const BitVectorBitOf& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const BitVectorBitOf& bv) {
  return os << "[" << bv.bitIndex << "]";
}

inline std::ostream& operator <<(std::ostream& os, const IntToBitVector& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const IntToBitVector& bv) {
  return os << "[" << bv.size << "]";
}

}/* CVC4 namespace */

#endif /* __CVC4__BITVECTOR_H */
