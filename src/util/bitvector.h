/*********************                                                        */
/*! \file bitvector.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A fixed-size bit-vector.
 **
 ** A fixed-size bit-vector, implemented as a wrapper around Integer.
 **/

#include "cvc4_public.h"

#ifndef CVC4__BITVECTOR_H
#define CVC4__BITVECTOR_H

#include <cstdint>
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

  /**
   * BitVector constructor using a 32-bit unsigned integer for the value.
   *
   * Note: we use an explicit bit-width here to be consistent across
   * platforms (long is 32-bit when compiling 64-bit binaries on
   * Windows but 64-bit on Linux) and to prevent ambiguous overloads.
   */
  BitVector(unsigned size, uint32_t z) : d_size(size), d_value(z)
  {
    d_value = d_value.modByPow2(size);
  }

  /**
   * BitVector constructor using a 64-bit unsigned integer for the value.
   *
   * Note: we use an explicit bit-width here to be consistent across
   * platforms (long is 32-bit when compiling 64-bit binaries on
   * Windows but 64-bit on Linux) and to prevent ambiguous overloads.
   */
  BitVector(unsigned size, uint64_t z) : d_size(size), d_value(z)
  {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, const BitVector& q)
      : d_size(size), d_value(q.d_value)
  {
  }

  /**
   * BitVector constructor.
   *
   * The value of the bit-vector is passed in as string of base 2, 10 or 16.
   * The size of resulting bit-vector is
   * - base  2: the size of the binary string
   * - base 10: the min. size required to represent the decimal as a bit-vector
   * - base 16: the max. size required to represent the hexadecimal as a
   *            bit-vector (4 * size of the given value string)
   *
   * @param num The value of the bit-vector in string representation.
   * @param base The base of the string representation.
   */
  BitVector(const std::string& num, unsigned base = 2)
  {
    CheckArgument(base == 2 || base == 10 || base == 16, base);
    d_value = Integer(num, base);
    switch (base)
    {
      case 10: d_size = d_value.length(); break;
      case 16: d_size = num.size() * 4; break;
      default: d_size = num.size();
    }
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
  unsigned d_high;
  /** The low bit of the range for this extract */
  unsigned d_low;

  BitVectorExtract(unsigned high, unsigned low) : d_high(high), d_low(low) {}

  bool operator==(const BitVectorExtract& extract) const
  {
    return d_high == extract.d_high && d_low == extract.d_low;
  }
}; /* struct BitVectorExtract */

/**
 * The structure representing the extraction of one Boolean bit.
 */
struct CVC4_PUBLIC BitVectorBitOf
{
  /** The index of the bit */
  unsigned d_bitIndex;
  BitVectorBitOf(unsigned i) : d_bitIndex(i) {}

  bool operator==(const BitVectorBitOf& other) const
  {
    return d_bitIndex == other.d_bitIndex;
  }
}; /* struct BitVectorBitOf */

struct CVC4_PUBLIC BitVectorSize
{
  unsigned d_size;
  BitVectorSize(unsigned size) : d_size(size) {}
  operator unsigned() const { return d_size; }
}; /* struct BitVectorSize */

struct CVC4_PUBLIC BitVectorRepeat
{
  unsigned d_repeatAmount;
  BitVectorRepeat(unsigned repeatAmount) : d_repeatAmount(repeatAmount) {}
  operator unsigned() const { return d_repeatAmount; }
}; /* struct BitVectorRepeat */

struct CVC4_PUBLIC BitVectorZeroExtend
{
  unsigned d_zeroExtendAmount;
  BitVectorZeroExtend(unsigned zeroExtendAmount)
      : d_zeroExtendAmount(zeroExtendAmount)
  {
  }
  operator unsigned() const { return d_zeroExtendAmount; }
}; /* struct BitVectorZeroExtend */

struct CVC4_PUBLIC BitVectorSignExtend
{
  unsigned d_signExtendAmount;
  BitVectorSignExtend(unsigned signExtendAmount)
      : d_signExtendAmount(signExtendAmount)
  {
  }
  operator unsigned() const { return d_signExtendAmount; }
}; /* struct BitVectorSignExtend */

struct CVC4_PUBLIC BitVectorRotateLeft
{
  unsigned d_rotateLeftAmount;
  BitVectorRotateLeft(unsigned rotateLeftAmount)
      : d_rotateLeftAmount(rotateLeftAmount)
  {
  }
  operator unsigned() const { return d_rotateLeftAmount; }
}; /* struct BitVectorRotateLeft */

struct CVC4_PUBLIC BitVectorRotateRight
{
  unsigned d_rotateRightAmount;
  BitVectorRotateRight(unsigned rotateRightAmount)
      : d_rotateRightAmount(rotateRightAmount)
  {
  }
  operator unsigned() const { return d_rotateRightAmount; }
}; /* struct BitVectorRotateRight */

struct CVC4_PUBLIC IntToBitVector
{
  unsigned d_size;
  IntToBitVector(unsigned size) : d_size(size) {}
  operator unsigned() const { return d_size; }
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
    size_t hash = extract.d_low;
    hash ^= extract.d_high + 0x9e3779b9 + (hash << 6) + (hash >> 2);
    return hash;
  }
}; /* struct BitVectorExtractHashFunction */

/**
 * Hash function for the BitVectorBitOf objects.
 */
struct CVC4_PUBLIC BitVectorBitOfHashFunction
{
  size_t operator()(const BitVectorBitOf& b) const { return b.d_bitIndex; }
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
  return os << "[" << bv.d_high << ":" << bv.d_low << "]";
}

inline std::ostream& operator<<(std::ostream& os,
                                const BitVectorBitOf& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const BitVectorBitOf& bv)
{
  return os << "[" << bv.d_bitIndex << "]";
}

inline std::ostream& operator<<(std::ostream& os,
                                const IntToBitVector& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const IntToBitVector& bv)
{
  return os << "[" << bv.d_size << "]";
}

}  // namespace CVC4

#endif /* CVC4__BITVECTOR_H */
