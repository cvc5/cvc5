/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A finite-field element, implemented as a wrapper around Integer.
 */

#include "util/finite_field_value.h"

#include "util/hash.h"

namespace cvc5::internal {

const Integer& FiniteFieldValue::getValue() const { return d_value; }

bool FiniteFieldValue::isZero() const { return d_value.isZero(); }

bool FiniteFieldValue::isOne() const { return d_value.isOne(); }

const Integer& FiniteFieldValue::getFieldSize() const { return d_size; }

Integer FiniteFieldValue::toInteger() const { return d_value; }

Integer FiniteFieldValue::toSignedInteger() const
{
  Integer half_size = d_size.d_val.divByPow2(1) + 1;
  return (d_value < half_size) ? d_value : d_value - d_size;
}

std::string FiniteFieldValue::toString() const
{
  return toSignedInteger().toString();
}

size_t FiniteFieldValue::hash() const
{
  PairHashFunction<size_t, size_t> h;
  return h(std::make_pair(d_value.hash(), d_size.d_val.hash()));
}

void FiniteFieldValue::normalize()
{
  d_value = d_value.floorDivideRemainder(d_size.d_val);
}

/* -----------------------------------------------------------------------
 * Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

bool operator==(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  if (x.d_size != y.d_size) return false;
  return x.d_value == y.d_value;
}

bool operator!=(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  if (x.d_size != y.d_size) return true;
  return x.d_value != y.d_value;
}

/* Unsigned Inequality --------------------------------------------------- */

bool operator<(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  return x.d_value < y.d_value;
}

bool operator<=(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  return x.d_value <= y.d_value;
}

bool operator>(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  return x.d_value > y.d_value;
}

bool operator>=(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  return x.d_value >= y.d_value;
}

/* Arithmetic operations ------------------------------------------------- */

FiniteFieldValue operator+(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  Assert(x.d_size == y.d_size)
      << "Size mismatch: " << x.d_size << " != " << y.d_size;
  Integer sum = x.d_value.modAdd(y.d_value, x.d_size);
  return {sum, x.d_size};
}

FiniteFieldValue operator-(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  Assert(x.d_size == y.d_size)
      << "Size mismatch: " << x.d_size << " != " << y.d_size;
  return {x.d_value - y.d_value, x.d_size};
}

FiniteFieldValue operator-(const FiniteFieldValue& x)
{
  return {x.d_size.d_val - x.d_value, x.d_size};
}

FiniteFieldValue operator*(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  Assert(x.d_size == y.d_size)
      << "Size mismatch: " << x.d_size << " != " << y.d_size;
  Integer prod = x.d_value.modMultiply(y.d_value, x.d_size);
  return {prod, x.d_size};
}

FiniteFieldValue operator/(const FiniteFieldValue& x, const FiniteFieldValue& y)
{
  return x * y.recip();
}

FiniteFieldValue FiniteFieldValue::recip() const
{
  Assert(!d_value.isZero());
  return {d_value.modInverse(d_size), d_size};
}

/* In-Place Arithmetic --------------------------------------------------- */

FiniteFieldValue& FiniteFieldValue::operator+=(const FiniteFieldValue& y)
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  d_value += y.d_value;
  normalize();
  return *this;
}

FiniteFieldValue& FiniteFieldValue::operator-=(const FiniteFieldValue& y)
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  d_value -= y.d_value;
  normalize();
  return *this;
}

FiniteFieldValue& FiniteFieldValue::operator*=(const FiniteFieldValue& y)
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  d_value *= y.d_value;
  normalize();
  return *this;
}

FiniteFieldValue& FiniteFieldValue::operator/=(const FiniteFieldValue& y)
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  d_value *= y.d_value.modInverse(d_size);
  normalize();
  return *this;
}


/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const FiniteFieldValue& ff)
{
  return os << ff.toString();
}

std::ostream& operator<<(std::ostream& os, const FfSize& ff)
{
  return os << ff.d_val;
}

/* -----------------------------------------------------------------------
 * Static helpers.
 * ----------------------------------------------------------------------- */

FiniteFieldValue FiniteFieldValue::mkZero(const Integer& size)
{
  return {0, size};
}

FiniteFieldValue FiniteFieldValue::mkOne(const Integer& size)
{
  return {1, size};
}

}  // namespace cvc5::internal
