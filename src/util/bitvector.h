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
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BITVECTOR_H
#define __CVC4__BITVECTOR_H

#include <iosfwd>

#include "base/exception.h"
#include "util/integer.h"

namespace CVC4 {

class CVC4_PUBLIC BitVector
{
 public:
  BitVector(unsigned size, const Integer& val)
      : d_size(size), d_value(val.modByPow2(size))
  {
  }

  BitVector(unsigned size = 0) : d_size(size), d_value(0) {}

  BitVector(unsigned size, unsigned int z) : d_size(size), d_value(z)
  {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, unsigned long int z) : d_size(size), d_value(z)
  {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, const BitVector& q)
      : d_size(size), d_value(q.d_value)
  {
  }

  BitVector(const std::string& num, unsigned base = 2)
  {
    CheckArgument(base == 2 || base == 16, base);
    d_size = base == 2 ? num.size() : num.size() * 4;
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

  /* Get size (bit-width). */
  unsigned getSize() const;
  /* Get value. */
  const Integer& getValue() const;

  /* Return value. */
  Integer toInteger() const;
  /* Return Integer corresponding to two's complement interpretation of this. */
  Integer toSignedInteger() const;
  /* Return (binary) string representation. */
  std::string toString(unsigned int base = 2) const;

  /* Return hash value. */
  size_t hash() const;

  /* Set bit at index 'i'. */
  BitVector setBit(uint32_t i) const;
  /* Return true if bit at index 'i' is set. */
  bool isBitSet(uint32_t i) const;

  /* Return k if the value of this is equal to 2^{k-1}, and zero otherwise. */
  unsigned isPow2() const;

  /* -----------------------------------------------------------------------
   ** Operators
   * ----------------------------------------------------------------------- */

  /* String Operations ----------------------------------------------------- */

  /* Return the concatenation of this and bit-vector 'other'. */
  BitVector concat(const BitVector& other) const;

  /* Return the bit range from index 'high' to index 'low'. */
  BitVector extract(unsigned high, unsigned low) const;

  /* (Dis)Equality --------------------------------------------------------- */

  /* Return true if this is equal to 'y'. */
  bool operator==(const BitVector& y) const;

  /* Return true if this is not equal to 'y'. */
  bool operator!=(const BitVector& y) const;

  /* Unsigned Inequality --------------------------------------------------- */

  /* Return true if this is unsigned less than bit-vector 'y'. */
  bool operator<(const BitVector& y) const;

  /* Return true if this is unsigned less than or equal to bit-vector 'y'. */
  bool operator<=(const BitVector& y) const;

  /* Return true if this is unsigned greater than bit-vector 'y'. */
  bool operator>(const BitVector& y) const;

  /* Return true if this is unsigned greater than or equal to bit-vector 'y'. */
  bool operator>=(const BitVector& y) const;

  /* Return true if this is unsigned less than bit-vector 'y'.
   * This function is a synonym for operator < but performs additional
   * argument checks.*/
  bool unsignedLessThan(const BitVector& y) const;

  /* Return true if this is unsigned less than or equal to bit-vector 'y'.
   * This function is a synonym for operator >= but performs additional
   * argument checks.*/
  bool unsignedLessThanEq(const BitVector& y) const;

  /* Signed Inequality ----------------------------------------------------- */

  /* Return true if this is signed less than bit-vector 'y'. */
  bool signedLessThan(const BitVector& y) const;

  /* Return true if this is signed less than or equal to bit-vector 'y'. */
  bool signedLessThanEq(const BitVector& y) const;

  /* Bit-wise operations --------------------------------------------------- */

  /* Return a bit-vector representing the bit-wise xor (this ^ y). */
  BitVector operator^(const BitVector& y) const;

  /* Return a bit-vector representing the bit-wise or (this | y). */
  BitVector operator|(const BitVector& y) const;

  /* Return a bit-vector representing the bit-wise and (this & y). */
  BitVector operator&(const BitVector& y) const;

  /* Return a bit-vector representing the bit-wise not of this. */
  BitVector operator~() const;

  /* Arithmetic operations ------------------------------------------------- */

  /* Return a bit-vector representing the addition (this + y). */
  BitVector operator+(const BitVector& y) const;

  /* Return a bit-vector representing the subtraction (this - y). */
  BitVector operator-(const BitVector& y) const;

  /* Return a bit-vector representing the negation of this. */
  BitVector operator-() const;

  /* Return a bit-vector representing the multiplication (this * y). */
  BitVector operator*(const BitVector& y) const;

  /* Total division function.
   * Returns a bit-vector representing 2^d_size-1 (signed: -1) when the
   * denominator is zero, and a bit-vector representing the unsigned division
   * (this / y), otherwise.  */
  BitVector unsignedDivTotal(const BitVector& y) const;

  /* Total remainder function.
   * Returns this when the denominator is zero, and the unsigned remainder
   * (this % y), otherwise.  */
  BitVector unsignedRemTotal(const BitVector& y) const;

  /* Extend operations ----------------------------------------------------- */

  /* Return a bit-vector representing this extended by 'n' zero bits. */
  BitVector zeroExtend(unsigned n) const;

  /* Return a bit-vector representing this extended by 'n' bits of the value
   * of the signed bit. */
  BitVector signExtend(unsigned n) const;

  /* Shift operations ------------------------------------------------------ */

  /* Return a bit-vector representing a left shift of this by 'y'. */
  BitVector leftShift(const BitVector& y) const;

  /* Return a bit-vector representing a logical right shift of this by 'y'. */
  BitVector logicalRightShift(const BitVector& y) const;

  /* Return a bit-vector representing an arithmetic right shift of this
   * by 'y'.*/
  BitVector arithRightShift(const BitVector& y) const;

  /* -----------------------------------------------------------------------
   ** Static helpers.
   * ----------------------------------------------------------------------- */

  /* Create bit-vector of ones of given size. */
  static BitVector mkOnes(unsigned size);

  /* Create bit-vector representing the minimum signed value of given size. */
  static BitVector mkMinSigned(unsigned size);

  /* Create bit-vector representing the maximum signed value of given size. */
  static BitVector mkMaxSigned(unsigned size);

 private:
  /**
   * Class invariants:
   *  - no overflows: 2^d_size < d_value
   *  - no negative numbers: d_value >= 0
   */

  unsigned d_size;
  Integer d_value;

}; /* class BitVector */

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
struct CVC4_PUBLIC BitVectorBitOf
{
  /** The index of the bit */
  unsigned bitIndex;
  BitVectorBitOf(unsigned i) : bitIndex(i) {}

  bool operator==(const BitVectorBitOf& other) const
  {
    return bitIndex == other.bitIndex;
  }
}; /* struct BitVectorBitOf */

struct CVC4_PUBLIC BitVectorSize
{
  unsigned size;
  BitVectorSize(unsigned size) : size(size) {}
  operator unsigned() const { return size; }
}; /* struct BitVectorSize */

struct CVC4_PUBLIC BitVectorRepeat
{
  unsigned repeatAmount;
  BitVectorRepeat(unsigned repeatAmount) : repeatAmount(repeatAmount) {}
  operator unsigned() const { return repeatAmount; }
}; /* struct BitVectorRepeat */

struct CVC4_PUBLIC BitVectorZeroExtend
{
  unsigned zeroExtendAmount;
  BitVectorZeroExtend(unsigned zeroExtendAmount)
      : zeroExtendAmount(zeroExtendAmount)
  {
  }
  operator unsigned() const { return zeroExtendAmount; }
}; /* struct BitVectorZeroExtend */

struct CVC4_PUBLIC BitVectorSignExtend
{
  unsigned signExtendAmount;
  BitVectorSignExtend(unsigned signExtendAmount)
      : signExtendAmount(signExtendAmount)
  {
  }
  operator unsigned() const { return signExtendAmount; }
}; /* struct BitVectorSignExtend */

struct CVC4_PUBLIC BitVectorRotateLeft
{
  unsigned rotateLeftAmount;
  BitVectorRotateLeft(unsigned rotateLeftAmount)
      : rotateLeftAmount(rotateLeftAmount)
  {
  }
  operator unsigned() const { return rotateLeftAmount; }
}; /* struct BitVectorRotateLeft */

struct CVC4_PUBLIC BitVectorRotateRight
{
  unsigned rotateRightAmount;
  BitVectorRotateRight(unsigned rotateRightAmount)
      : rotateRightAmount(rotateRightAmount)
  {
  }
  operator unsigned() const { return rotateRightAmount; }
}; /* struct BitVectorRotateRight */

struct CVC4_PUBLIC IntToBitVector
{
  unsigned size;
  IntToBitVector(unsigned size) : size(size) {}
  operator unsigned() const { return size; }
}; /* struct IntToBitVector */

/* -----------------------------------------------------------------------
 ** Hash Function structs
 * ----------------------------------------------------------------------- */

/*
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC BitVectorHashFunction
{
  inline size_t operator()(const BitVector& bv) const { return bv.hash(); }
}; /* struct BitVectorHashFunction */

/**
 * Hash function for the BitVectorExtract objects.
 */
struct CVC4_PUBLIC BitVectorExtractHashFunction
{
  size_t operator()(const BitVectorExtract& extract) const
  {
    size_t hash = extract.low;
    hash ^= extract.high + 0x9e3779b9 + (hash << 6) + (hash >> 2);
    return hash;
  }
}; /* struct BitVectorExtractHashFunction */

/**
 * Hash function for the BitVectorBitOf objects.
 */
struct CVC4_PUBLIC BitVectorBitOfHashFunction
{
  size_t operator()(const BitVectorBitOf& b) const { return b.bitIndex; }
}; /* struct BitVectorBitOfHashFunction */

template <typename T>
struct CVC4_PUBLIC UnsignedHashFunction
{
  inline size_t operator()(const T& x) const { return (size_t)x; }
}; /* struct UnsignedHashFunction */

/* -----------------------------------------------------------------------
 ** Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os,
                                const BitVector& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const BitVector& bv)
{
  return os << bv.toString();
}

inline std::ostream& operator<<(std::ostream& os,
                                const BitVectorExtract& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const BitVectorExtract& bv)
{
  return os << "[" << bv.high << ":" << bv.low << "]";
}

inline std::ostream& operator<<(std::ostream& os,
                                const BitVectorBitOf& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const BitVectorBitOf& bv)
{
  return os << "[" << bv.bitIndex << "]";
}

inline std::ostream& operator<<(std::ostream& os,
                                const IntToBitVector& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const IntToBitVector& bv)
{
  return os << "[" << bv.size << "]";
}

}  // namespace CVC4

#endif /* __CVC4__BITVECTOR_H */
