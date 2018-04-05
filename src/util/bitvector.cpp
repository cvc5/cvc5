/*********************                                                        */
/*! \file bitvector.cpp
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

#include "util/bitvector.h"

namespace CVC4 {

unsigned BitVector::getSize() const { return d_size; }

const Integer& BitVector::getValue() const { return d_value; }

Integer BitVector::toInteger() const { return d_value; }

Integer BitVector::toSignedInteger() const
{
  unsigned size = d_size;
  Integer sign_bit = d_value.extractBitRange(1, size - 1);
  Integer val = d_value.extractBitRange(size - 1, 0);
  Integer res = Integer(-1) * sign_bit.multiplyByPow2(size - 1) + val;
  return res;
}

std::string BitVector::toString(unsigned int base) const
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

size_t BitVector::hash() const
{
  return d_value.hash() + d_size;
}

BitVector BitVector::setBit(uint32_t i) const
{
  CheckArgument(i < d_size, i);
  Integer res = d_value.setBit(i);
  return BitVector(d_size, res);
}

bool BitVector::isBitSet(uint32_t i) const
{
  CheckArgument(i < d_size, i);
  return d_value.isBitSet(i);
}

unsigned BitVector::isPow2() const
{
  return d_value.isPow2();
}

/* -----------------------------------------------------------------------
 ** Operators
 * ----------------------------------------------------------------------- */

/* String Operations ----------------------------------------------------- */

BitVector BitVector::concat(const BitVector& other) const
{
  return BitVector(d_size + other.d_size,
                   (d_value.multiplyByPow2(other.d_size)) + other.d_value);
}

BitVector BitVector::extract(unsigned high, unsigned low) const
{
  CheckArgument(high < d_size, high);
  CheckArgument(low <= high, low);
  return BitVector(high - low + 1,
                   d_value.extractBitRange(high - low + 1, low));
}

/* (Dis)Equality --------------------------------------------------------- */

bool BitVector::operator==(const BitVector& y) const
{
  if (d_size != y.d_size) return false;
  return d_value == y.d_value;
}

bool BitVector::operator!=(const BitVector& y) const
{
  if (d_size != y.d_size) return true;
  return d_value != y.d_value;
}

/* Unsigned Inequality --------------------------------------------------- */

bool BitVector::operator<(const BitVector& y) const
{
  return d_value < y.d_value;
}

bool BitVector::operator<=(const BitVector& y) const
{
  return d_value <= y.d_value;
}

bool BitVector::operator>(const BitVector& y) const
{
  return d_value > y.d_value;
}

bool BitVector::operator>=(const BitVector& y) const
{
  return d_value >= y.d_value;
}

bool BitVector::unsignedLessThan(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  CheckArgument(d_value >= 0, this);
  CheckArgument(y.d_value >= 0, y);
  return d_value < y.d_value;
}

bool BitVector::unsignedLessThanEq(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, this);
  CheckArgument(d_value >= 0, this);
  CheckArgument(y.d_value >= 0, y);
  return d_value <= y.d_value;
}

/* Signed Inequality ----------------------------------------------------- */

bool BitVector::signedLessThan(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  CheckArgument(d_value >= 0, this);
  CheckArgument(y.d_value >= 0, y);
  Integer a = (*this).toSignedInteger();
  Integer b = y.toSignedInteger();

  return a < b;
}

bool BitVector::signedLessThanEq(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  CheckArgument(d_value >= 0, this);
  CheckArgument(y.d_value >= 0, y);
  Integer a = (*this).toSignedInteger();
  Integer b = y.toSignedInteger();

  return a <= b;
}

/* Bit-wise operations --------------------------------------------------- */

BitVector BitVector::operator^(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  return BitVector(d_size, d_value.bitwiseXor(y.d_value));
}

BitVector BitVector::operator|(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  return BitVector(d_size, d_value.bitwiseOr(y.d_value));
}

BitVector BitVector::operator&(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  return BitVector(d_size, d_value.bitwiseAnd(y.d_value));
}

BitVector BitVector::operator~() const
{
  return BitVector(d_size, d_value.bitwiseNot());
}

/* Arithmetic operations ------------------------------------------------- */

BitVector BitVector::operator+(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  Integer sum = d_value + y.d_value;
  return BitVector(d_size, sum);
}

BitVector BitVector::operator-(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  // to maintain the invariant that we are only adding BitVectors of the
  // same size
  BitVector one(d_size, Integer(1));
  return *this + ~y + one;
}

BitVector BitVector::operator-() const
{
  BitVector one(d_size, Integer(1));
  return ~(*this) + one;
}

BitVector BitVector::operator*(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  Integer prod = d_value * y.d_value;
  return BitVector(d_size, prod);
}

BitVector BitVector::unsignedDivTotal(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  /* d_value / 0 = -1 = 2^d_size - 1 */
  if (y.d_value == 0)
  {
    return BitVector(d_size, Integer(1).oneExtend(1, d_size - 1));
  }
  CheckArgument(d_value >= 0, this);
  CheckArgument(y.d_value > 0, y);
  return BitVector(d_size, d_value.floorDivideQuotient(y.d_value));
}

BitVector BitVector::unsignedRemTotal(const BitVector& y) const
{
  CheckArgument(d_size == y.d_size, y);
  if (y.d_value == 0)
  {
    return BitVector(d_size, d_value);
  }
  CheckArgument(d_value >= 0, this);
  CheckArgument(y.d_value > 0, y);
  return BitVector(d_size, d_value.floorDivideRemainder(y.d_value));
}

/* Extend operations ----------------------------------------------------- */

BitVector BitVector::zeroExtend(unsigned n) const
{
  return BitVector(d_size + n, d_value);
}

BitVector BitVector::signExtend(unsigned n) const
{
  Integer sign_bit = d_value.extractBitRange(1, d_size - 1);
  if (sign_bit == Integer(0))
  {
    return BitVector(d_size + n, d_value);
  }
  Integer val = d_value.oneExtend(d_size, n);
  return BitVector(d_size + n, val);
}

/* Shift operations ------------------------------------------------------ */

BitVector BitVector::leftShift(const BitVector& y) const
{
  if (y.d_value > Integer(d_size))
  {
    return BitVector(d_size, Integer(0));
  }
  if (y.d_value == 0)
  {
    return *this;
  }
  // making sure we don't lose information casting
  CheckArgument(y.d_value < Integer(1).multiplyByPow2(32), y);
  uint32_t amount = y.d_value.toUnsignedInt();
  Integer res = d_value.multiplyByPow2(amount);
  return BitVector(d_size, res);
}

BitVector BitVector::logicalRightShift(const BitVector& y) const
{
  if (y.d_value > Integer(d_size))
  {
    return BitVector(d_size, Integer(0));
  }
  // making sure we don't lose information casting
  CheckArgument(y.d_value < Integer(1).multiplyByPow2(32), y);
  uint32_t amount = y.d_value.toUnsignedInt();
  Integer res = d_value.divByPow2(amount);
  return BitVector(d_size, res);
}

BitVector BitVector::arithRightShift(const BitVector& y) const
{
  Integer sign_bit = d_value.extractBitRange(1, d_size - 1);
  if (y.d_value > Integer(d_size))
  {
    if (sign_bit == Integer(0))
    {
      return BitVector(d_size, Integer(0));
    }
    else
    {
      return BitVector(d_size, Integer(d_size).multiplyByPow2(d_size) - 1);
    }
  }

  if (y.d_value == 0)
  {
    return *this;
  }

  // making sure we don't lose information casting
  CheckArgument(y.d_value < Integer(1).multiplyByPow2(32), y);

  uint32_t amount = y.d_value.toUnsignedInt();
  Integer rest = d_value.divByPow2(amount);

  if (sign_bit == Integer(0))
  {
    return BitVector(d_size, rest);
  }
  Integer res = rest.oneExtend(d_size - amount, amount);
  return BitVector(d_size, res);
}

/* -----------------------------------------------------------------------
 ** Static helpers.
 * ----------------------------------------------------------------------- */

BitVector BitVector::mkOnes(unsigned size)
{
  CheckArgument(size > 0, size);
  return BitVector(1, Integer(1)).signExtend(size - 1);
}

BitVector BitVector::mkMinSigned(unsigned size)
{
  CheckArgument(size > 0, size);
  return BitVector(size).setBit(size - 1);
}

BitVector BitVector::mkMaxSigned(unsigned size)
{
  CheckArgument(size > 0, size);
  return ~BitVector::mkMinSigned(size);
}

}  // namespace CVC4
