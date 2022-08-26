/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A finite-field element, implemented as a wrapper around Integer.
 */

#include "util/ff_val.h"

#include "util/hash.h"

namespace cvc5::internal {

const Integer& FfVal::getValue() const { return d_value; }

const Integer& FfVal::getFieldSize() const { return d_size; }

Integer FfVal::toInteger() const { return d_value; }

Integer FfVal::toSignedInteger() const
{
  Integer half_size = d_size.divByPow2(1) + 1;
  return (d_value < half_size) ? d_value : d_value - d_size;
}

std::string FfVal::toString() const
{
  return toSignedInteger().toString();
}

size_t FfVal::hash() const
{
  PairHashFunction<size_t, size_t> h;
  return h(std::make_pair(d_value.hash(), d_size.hash()));
}

/* -----------------------------------------------------------------------
 * Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

bool operator==(const FfVal& x, const FfVal& y)
{
  if (x.d_size != y.d_size) return false;
  return x.d_value == y.d_value;
}

bool operator!=(const FfVal& x, const FfVal& y)
{
  if (x.d_size != y.d_size) return true;
  return x.d_value != y.d_value;
}

/* Unsigned Inequality --------------------------------------------------- */

bool operator<(const FfVal& x, const FfVal& y)
{
  return x.d_value < y.d_value;
}

bool operator<=(const FfVal& x, const FfVal& y)
{
  return x.d_value <= y.d_value;
}

bool operator>(const FfVal& x, const FfVal& y)
{
  return x.d_value > y.d_value;
}

bool operator>=(const FfVal& x, const FfVal& y)
{
  return x.d_value >= y.d_value;
}

/* Arithmetic operations ------------------------------------------------- */

FfVal operator+(const FfVal& x, const FfVal& y)
{
  Assert(x.d_size == y.d_size)
      << "Size mismatch: " << x.d_size << " != " << y.d_size;
  Integer sum = x.d_value.modAdd(y.d_value, x.d_size);
  return {sum, x.d_size};
}

FfVal operator-(const FfVal& x, const FfVal& y)
{
  Assert(x.d_size == y.d_size)
      << "Size mismatch: " << x.d_size << " != " << y.d_size;
  return {x.d_value - y.d_value, x.d_size};
}

FfVal operator-(const FfVal& x)
{
  return {x.d_size - x.d_value, x.d_size};
}

FfVal operator*(const FfVal& x, const FfVal& y)
{
  Assert(x.d_size == y.d_size)
      << "Size mismatch: " << x.d_size << " != " << y.d_size;
  Integer prod = x.d_value.modMultiply(y.d_value, x.d_size);
  return {prod, x.d_size};
}

FfVal operator/(const FfVal& x, const FfVal& y)
{
  return x * y.recip();
}

FfVal FfVal::recip() const
{
  Assert(!d_value.isZero());
  return {d_value.modInverse(d_size), d_size};
}

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const FfVal& ff)
{
  return os << ff.toString();
}

/* -----------------------------------------------------------------------
 * Static helpers.
 * ----------------------------------------------------------------------- */

FfVal FfVal::mkZero(const Integer& size) { return {0, size}; }

FfVal FfVal::mkOne(const Integer& size) { return {1, size}; }

}  // namespace cvc5::internal
