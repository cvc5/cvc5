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

#include "util/finite_field.h"

#include "base/exception.h"

namespace cvc5::internal {

const Integer& FiniteField::getValue() const { return d_value; }

const Integer& FiniteField::getFieldSize() const { return d_size; }

Integer FiniteField::toInteger() const { return d_value; }

Integer FiniteField::toSignedInteger() const
{
  Integer half_size = d_size.divByPow2(1) + 1;
  return (d_value < half_size) ? d_value : d_value - d_size;
}

std::string FiniteField::toString(unsigned int base) const
{
  return toSignedInteger().toString();
}

size_t FiniteField::hash() const { return d_value.hash() + d_size.hash(); }

/* -----------------------------------------------------------------------
 * Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

bool FiniteField::operator==(const FiniteField& y) const
{
  if (d_size != y.d_size) return false;
  return d_value == y.d_value;
}

bool FiniteField::operator!=(const FiniteField& y) const
{
  if (d_size != y.d_size) return true;
  return d_value != y.d_value;
}

/* Unsigned Inequality --------------------------------------------------- */

bool FiniteField::operator<(const FiniteField& y) const
{
  return d_value < y.d_value;
}

bool FiniteField::operator<=(const FiniteField& y) const
{
  return d_value <= y.d_value;
}

bool FiniteField::operator>(const FiniteField& y) const
{
  return d_value > y.d_value;
}

bool FiniteField::operator>=(const FiniteField& y) const
{
  return d_value >= y.d_value;
}

/* Arithmetic operations ------------------------------------------------- */

FiniteField FiniteField::operator+(const FiniteField& y) const
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  Integer sum = d_value.modAdd(y.d_value, d_size);
  return {sum, d_size};
}

FiniteField FiniteField::operator-(const FiniteField& y) const
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  return {d_value - y.d_value, d_size};
}

FiniteField FiniteField::operator-() const
{
  return {d_size - d_value, d_size};
}

FiniteField FiniteField::operator*(const FiniteField& y) const
{
  Assert(d_size == y.d_size)
      << "Size mismatch: " << d_size << " != " << y.d_size;
  Integer prod = d_value.modMultiply(y.d_value, d_size);
  return {prod, d_size};
}

FiniteField FiniteField::operator/(const FiniteField& y) const
{
  return *this * y.recip();
}

FiniteField FiniteField::recip() const
{
  CheckArgument(!d_value.isZero(), *this);
  return {d_value.modInverse(d_size), d_size};
}

/* -----------------------------------------------------------------------
 * Static helpers.
 * ----------------------------------------------------------------------- */

FiniteField FiniteField::mkZero(const Integer& size) { return {0, size}; }

FiniteField FiniteField::mkOne(const Integer& size) { return {1, size}; }

}  // namespace cvc5::internal
