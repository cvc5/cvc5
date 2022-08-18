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
 *
 * TODOs:
 * * consider montgomery form
 * * extend to non-prime fields
 */

#include "cvc5_public.h"

#ifndef CVC5__FINITE_FIELD_H
#define CVC5__FINITE_FIELD_H

#include <iosfwd>

#include "base/check.h"
#include "base/exception.h"
#include "util/integer.h"

namespace cvc5::internal {

class FiniteField
{
 public:
  FiniteField(const Integer& val, const Integer& size)
      : d_size(size),
        // normalize value into [0, size)
        d_value(val.floorDivideRemainder(size))
  {
    // we only support prime fields right now
    Assert(size.isProbablePrime());
  }

  /**
   * Construct the zero in this field
   */
  FiniteField(const Integer& size) : d_size(size), d_value(0)
  {
    // we only support prime fields right now
    Assert(size.isProbablePrime());
  }

  ~FiniteField() {}

  FiniteField& operator=(const FiniteField& x)
  {
    if (this == &x) return *this;
    d_size = x.d_size;
    d_value = x.d_value;
    return *this;
  }

  /* Get value. */
  const Integer& getValue() const;

  /* Get field size. */
  const Integer& getFieldSize() const;

  /* Return value. */
  Integer toInteger() const;
  /* Return Integer of smallest absolute value that represents this.
   *
   * For fields of odd size, there is always a unique representative of
   * smallest absolute value.
   *
   * For GF(2), the multiplicative identity is represented as "1", not "-1".
   * */
  Integer toSignedInteger() const;
  /* Return string representation (of the value as a signed integer). */
  std::string toString() const;

  /* Return hash value. */
  size_t hash() const;

  friend bool operator==(const FiniteField&, const FiniteField&);
  friend bool operator!=(const FiniteField&, const FiniteField&);
  friend bool operator<(const FiniteField&, const FiniteField&);
  friend bool operator>(const FiniteField&, const FiniteField&);
  friend bool operator>=(const FiniteField&, const FiniteField&);
  friend bool operator<=(const FiniteField&, const FiniteField&);
  friend FiniteField operator+(const FiniteField&, const FiniteField&);
  friend FiniteField operator-(const FiniteField&, const FiniteField&);
  friend FiniteField operator-(const FiniteField&);
  friend FiniteField operator*(const FiniteField&, const FiniteField&);
  friend FiniteField operator/(const FiniteField&, const FiniteField&);

  /* Reciprocal. Crashes on 0. */
  FiniteField recip() const;

  /* -----------------------------------------------------------------------
   ** Static helpers.
   * ----------------------------------------------------------------------- */

  /* Create zero bit-vector of given size. */
  static FiniteField mkZero(const Integer& modulus);

  /* Create bit-vector representing value 1 of given size. */
  static FiniteField mkOne(const Integer& modulus);

 private:
  /**
   * Class invariants:
   *  - no overflows: d_value < d_modulus
   *  - no negative numbers: d_value >= 0
   */

  Integer d_size;
  Integer d_value;

}; /* class FiniteField */

struct FiniteFieldSize
{
  FiniteFieldSize(Integer size) : d_size(size) {}
  operator Integer() const { return d_size; }
  bool operator==(const FiniteFieldSize& y) const
  {
    return d_size == y.d_size;
  }
  
  Integer d_size;
}; /* struct FiniteFieldSize */

/*
 * Hash function for the FiniteField constants.
 */
struct FiniteFieldHashFunction
{
  size_t operator()(const FiniteField& ff) const { return ff.hash(); }
}; /* struct FiniteFieldHashFunction */

/*
 * Hash function for the FiniteFieldSize constants.
 */
struct FiniteFieldSizeHashFunction
{
  size_t operator()(const FiniteFieldSize& size) const
  {
    return size.d_size.hash();
  }
}; /* struct FiniteFieldHashFunction */

/* -----------------------------------------------------------------------
 ** Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

/* Return true if x is equal to 'y'. */
bool operator==(const FiniteField& x, const FiniteField& y);

/* Return true if x is not equal to 'y'. */
bool operator!=(const FiniteField& x, const FiniteField& y);

/* Unsigned Inequality --------------------------------------------------- */

/* Return true if x is unsigned less than finite field 'y'. */
bool operator<(const FiniteField& x, const FiniteField& y);

/* Return true if x is unsigned less than or equal to finite field 'y'. */
bool operator<=(const FiniteField& x, const FiniteField& y);

/* Return true if x is unsigned greater than finite field 'y'. */
bool operator>(const FiniteField& x, const FiniteField& y);

/* Return true if x is unsigned greater than or equal to finite field 'y'. */
bool operator>=(const FiniteField& x, const FiniteField& y);

/* Arithmetic operations ------------------------------------------------- */

/* Return a finite field representing the addition (x + y). */
FiniteField operator+(const FiniteField& x, const FiniteField& y);

/* Return a finite field representing the subtraction (x - y). */
FiniteField operator-(const FiniteField& x, const FiniteField& y);

/* Return a finite field representing the negation of x. */
FiniteField operator-(const FiniteField& x);

/* Return a finite field representing the multiplication (x * y). */
FiniteField operator*(const FiniteField& x, const FiniteField& y);

/* Return a finite field representing the division (x / y). */
FiniteField operator/(const FiniteField& x, const FiniteField& y);

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const FiniteField& ff)
{
  return os << ff.toString();
}

}  // namespace cvc5::internal

#endif /* CVC5__FINITE_FIELD_H */
