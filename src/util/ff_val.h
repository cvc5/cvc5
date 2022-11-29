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

class FfVal
{
 public:
  FfVal(const Integer& val, const Integer& size)
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
  FfVal(const Integer& size) : d_size(size), d_value(0)
  {
    // we only support prime fields right now
    Assert(size.isProbablePrime());
  }

  ~FfVal() {}

  FfVal& operator=(const FfVal& x)
  {
    if (this == &x)
    {
      return *this;
    }
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

  friend bool operator==(const FfVal&, const FfVal&);
  friend bool operator!=(const FfVal&, const FfVal&);
  friend bool operator<(const FfVal&, const FfVal&);
  friend bool operator>(const FfVal&, const FfVal&);
  friend bool operator>=(const FfVal&, const FfVal&);
  friend bool operator<=(const FfVal&, const FfVal&);
  friend FfVal operator+(const FfVal&, const FfVal&);
  friend FfVal operator-(const FfVal&, const FfVal&);
  friend FfVal operator-(const FfVal&);
  friend FfVal operator*(const FfVal&, const FfVal&);
  friend FfVal operator/(const FfVal&, const FfVal&);

  /* Reciprocal. Crashes on 0. */
  FfVal recip() const;

  /* -----------------------------------------------------------------------
   ** Static helpers.
   * ----------------------------------------------------------------------- */

  /* Create zero bit-vector of given size. */
  static FfVal mkZero(const Integer& modulus);

  /* Create bit-vector representing value 1 of given size. */
  static FfVal mkOne(const Integer& modulus);

 private:
  /**
   * Class invariants:
   *  - no overflows: d_value < d_modulus
   *  - no negative numbers: d_value >= 0
   */

  Integer d_size;
  Integer d_value;

}; /* class FfVal */

struct FfSize
{
  FfSize(Integer size) : d_size(size) {}
  operator const Integer&() const { return d_size; }
  bool operator==(const FfSize& y) const
  {
    return d_size == y.d_size;
  }
  
  Integer d_size;
}; /* struct FfSize */

/*
 * Hash function for the FfVal.
 */
struct FfValHashFunction
{
  size_t operator()(const FfVal& ff) const { return ff.hash(); }
}; /* struct FfValHashFunction */

/*
 * Hash function for the FfSize constants.
 */
struct FfSizeHashFunction
{
  size_t operator()(const FfSize& size) const
  {
    return size.d_size.hash();
  }
}; /* struct FfValHashFunction */

/* -----------------------------------------------------------------------
 ** Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

/* Return true if x is equal to 'y'. */
bool operator==(const FfVal& x, const FfVal& y);

/* Return true if x is not equal to 'y'. */
bool operator!=(const FfVal& x, const FfVal& y);

/* Unsigned Inequality --------------------------------------------------- */

/* Return true if x is unsigned less than finite field 'y'. */
bool operator<(const FfVal& x, const FfVal& y);

/* Return true if x is unsigned less than or equal to finite field 'y'. */
bool operator<=(const FfVal& x, const FfVal& y);

/* Return true if x is unsigned greater than finite field 'y'. */
bool operator>(const FfVal& x, const FfVal& y);

/* Return true if x is unsigned greater than or equal to finite field 'y'. */
bool operator>=(const FfVal& x, const FfVal& y);

/* Arithmetic operations ------------------------------------------------- */

/* Return a finite field representing the addition (x + y). */
FfVal operator+(const FfVal& x, const FfVal& y);

/* Return a finite field representing the subtraction (x - y). */
FfVal operator-(const FfVal& x, const FfVal& y);

/* Return a finite field representing the negation of x. */
FfVal operator-(const FfVal& x);

/* Return a finite field representing the multiplication (x * y). */
FfVal operator*(const FfVal& x, const FfVal& y);

/* Return a finite field representing the division (x / y). */
FfVal operator/(const FfVal& x, const FfVal& y);

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const FfVal& ff);

}  // namespace cvc5::internal

#endif /* CVC5__FINITE_FIELD_H */
