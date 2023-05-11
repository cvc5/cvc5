/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A fixed-size bit-vector, implemented as a wrapper around Integer.
 */

#include "util/bitvector.h"

#include "base/check.h"
#include "util/hash.h"

namespace cvc5::internal {

BitVector::BitVector(const std::string& num, uint32_t base)
{
  Assert(base == 2 || base == 10 || base == 16);
  Assert(num[0] != '-');
  d_value = Integer(num, base);
  Assert(d_value == d_value.abs());
  // Compute the length, *without* any negative sign.
  switch (base)
  {
    case 10: d_size = d_value.length(); break;
    case 16: d_size = num.size() * 4; break;
    default: d_size = num.size();
  }
}

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
  PairHashFunction<size_t, size_t> h;
  return h(std::make_pair(d_value.hash(), d_size));
}

BitVector& BitVector::setBit(uint32_t i, bool value)
{
  Assert(i < d_size);
  d_value.setBit(i, value);
  return *this;
}

bool BitVector::isBitSet(uint32_t i) const
{
  Assert(i < d_size);
  return d_value.isBitSet(i);
}

unsigned BitVector::isPow2() const
{
  return d_value.isPow2();
}

/* -----------------------------------------------------------------------
 * Operators
 * ----------------------------------------------------------------------- */

/* String Operations ----------------------------------------------------- */

BitVector BitVector::concat(const BitVector& other) const
{
  return BitVector(d_size + other.d_size,
                   (d_value.multiplyByPow2(other.d_size)) + other.d_value);
}

BitVector BitVector::extract(unsigned high, unsigned low) const
{
  Assert(high < d_size);
  Assert(low <= high);
  return BitVector(high - low + 1,
                   d_value.extractBitRange(high - low + 1, low));
}

/* (Dis)Equality --------------------------------------------------------- */

bool operator==(const BitVector& a, const BitVector& b)
{
  if (a.getSize() != b.getSize()) return false;
  return a.getValue() == b.getValue();
}

bool operator!=(const BitVector& a, const BitVector& b)
{
  if (a.getSize() != b.getSize()) return true;
  return a.getValue() != b.getValue();
}

/* Unsigned Inequality --------------------------------------------------- */

bool operator<(const BitVector& a, const BitVector& b)
{
  return a.getValue() < b.getValue();
}

bool operator<=(const BitVector& a, const BitVector& b)
{
  return a.getValue() <= b.getValue();
}

bool operator>(const BitVector& a, const BitVector& b)
{
  return a.getValue() > b.getValue();
}

bool operator>=(const BitVector& a, const BitVector& b)
{
  return a.getValue() >= b.getValue();
}

bool BitVector::unsignedLessThan(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  Assert(d_value >= 0);
  Assert(y.d_value >= 0);
  return d_value < y.d_value;
}

bool BitVector::unsignedLessThanEq(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  Assert(d_value >= 0);
  Assert(y.d_value >= 0);
  return d_value <= y.d_value;
}

/* Signed Inequality ----------------------------------------------------- */

bool BitVector::signedLessThan(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  Assert(d_value >= 0);
  Assert(y.d_value >= 0);
  Integer a = (*this).toSignedInteger();
  Integer b = y.toSignedInteger();

  return a < b;
}

bool BitVector::signedLessThanEq(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  Assert(d_value >= 0);
  Assert(y.d_value >= 0);
  Integer a = (*this).toSignedInteger();
  Integer b = y.toSignedInteger();

  return a <= b;
}

/* Bit-wise operations --------------------------------------------------- */

BitVector operator^(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  return BitVector(a.getSize(), a.getValue().bitwiseXor(b.getValue()));
}

BitVector operator|(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  return BitVector(a.getSize(), a.getValue().bitwiseOr(b.getValue()));
}

BitVector operator&(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  return BitVector(a.getSize(), a.getValue().bitwiseAnd(b.getValue()));
}

BitVector operator~(const BitVector& a)
{
  return BitVector(a.getSize(), a.getValue().bitwiseNot());
}

/* Arithmetic operations ------------------------------------------------- */

BitVector operator+(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  Integer sum = a.getValue() + b.getValue();
  return BitVector(a.getSize(), sum);
}

BitVector operator-(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  // to maintain the invariant that we are only adding BitVectors of the
  // same size
  BitVector one(a.getSize(), Integer(1));
  return a + ~b + one;
}

BitVector operator-(const BitVector& a)
{
  BitVector one(a.getSize(), Integer(1));
  return ~a + one;
}

BitVector operator*(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  Integer prod = a.getValue() * b.getValue();
  return BitVector(a.getSize(), prod);
}

BitVector BitVector::unsignedDivTotal(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  /* d_value / 0 = -1 = 2^d_size - 1 */
  if (y.d_value == 0)
  {
    return BitVector(d_size, Integer(1).oneExtend(1, d_size - 1));
  }
  Assert(d_value >= 0);
  Assert(y.d_value > 0);
  return BitVector(d_size, d_value.floorDivideQuotient(y.d_value));
}

BitVector BitVector::unsignedRemTotal(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  if (y.d_value == 0)
  {
    return BitVector(d_size, d_value);
  }
  Assert(d_value >= 0);
  Assert(y.d_value > 0);
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
  Assert(y.d_value < Integer(1).multiplyByPow2(32));
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
  Assert(y.d_value < Integer(1).multiplyByPow2(32));
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
  Assert(y.d_value < Integer(1).multiplyByPow2(32));

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
 * Static helpers.
 * ----------------------------------------------------------------------- */

BitVector BitVector::mkZero(unsigned size)
{
  Assert(size > 0);
  return BitVector(size);
}

BitVector BitVector::mkOne(unsigned size)
{
  Assert(size > 0);
  return BitVector(size, 1u);
}

BitVector BitVector::mkOnes(unsigned size)
{
  Assert(size > 0);
  return BitVector(1, Integer(1)).signExtend(size - 1);
}

BitVector BitVector::mkMinSigned(unsigned size)
{
  Assert(size > 0);
  BitVector res(size);
  res.setBit(size - 1, true);
  return res;
}

BitVector BitVector::mkMaxSigned(unsigned size)
{
  Assert(size > 0);
  return ~BitVector::mkMinSigned(size);
}

}  // namespace cvc5::internal
