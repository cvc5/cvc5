/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A finite-field element, implemented as a wrapper around Integer.
 *
 * TODOs:
 * * extend to non-prime fields
 * (https://github.com/cvc5/cvc5-wishues/issues/139)
 * * consider montgomery form (https://github.com/cvc5/cvc5-wishues/issues/140)
 */

#include "cvc5_public.h"

#ifndef CVC5__FINITE_FIELDVALUE_H
#define CVC5__FINITE_FIELDVALUE_H

#include <iosfwd>

#include "base/check.h"
#include "base/exception.h"
#include "util/integer.h"

namespace cvc5::internal {

/** Stores a field size that have been validated to be prime */
struct FfSize
{
  FfSize(Integer size) : d_val(size)
  {
    // we only support prime fields right now
    Assert(size.isProbablePrime()) << "not prime: " << size;
  }
  FfSize(int size) : d_val(size)
  {
    // we only support prime fields right now
    Assert(d_val.isProbablePrime()) << "not prime: " << size;
  }
  FfSize(size_t size) : d_val(size)
  {
    // we only support prime fields right now
    Assert(d_val.isProbablePrime()) << "not prime: " << size;
  }
  operator const Integer&() const { return d_val; }
  bool operator==(const FfSize& y) const { return d_val == y.d_val; }
  bool operator!=(const FfSize& y) const { return d_val != y.d_val; }

  Integer d_val;
}; /* struct FfSize */

class FiniteFieldValue
{
 public:
  FiniteFieldValue(const Integer& val, const FfSize& size)
      : d_size(size),
        // normalize value into [0, size)
        d_value(val.floorDivideRemainder(size))
  {
  }

  /**
   * Construct the zero in this field
   */
  FiniteFieldValue(const FfSize& size) : d_size(size), d_value(0) {}

  ~FiniteFieldValue() {}

  FiniteFieldValue& operator=(const FiniteFieldValue& x)
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

  /* Is zero? */
  bool isZero() const;

  /* Is one? */
  bool isOne() const;

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

  friend bool operator==(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator!=(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator<(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator>(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator>=(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator<=(const FiniteFieldValue&, const FiniteFieldValue&);
  friend FiniteFieldValue operator+(const FiniteFieldValue&,
                                    const FiniteFieldValue&);
  friend FiniteFieldValue operator-(const FiniteFieldValue&,
                                    const FiniteFieldValue&);
  friend FiniteFieldValue operator-(const FiniteFieldValue&);
  friend FiniteFieldValue operator*(const FiniteFieldValue&,
                                    const FiniteFieldValue&);
  friend FiniteFieldValue operator/(const FiniteFieldValue&,
                                    const FiniteFieldValue&);

  FiniteFieldValue& operator+=(const FiniteFieldValue&);
  FiniteFieldValue& operator-=(const FiniteFieldValue&);
  FiniteFieldValue& operator*=(const FiniteFieldValue&);
  FiniteFieldValue& operator/=(const FiniteFieldValue&);

  /* Reciprocal. Crashes on 0. */
  FiniteFieldValue recip() const;

  /* -----------------------------------------------------------------------
   ** Static helpers.
   * ----------------------------------------------------------------------- */

  /* Create zero bit-vector of given size. */
  static FiniteFieldValue mkZero(const Integer& modulus);

  /* Create bit-vector representing value 1 of given size. */
  static FiniteFieldValue mkOne(const Integer& modulus);

 private:
  /** bring d_value back into the range below */
  void normalize();

  /**
   * Class invariants:
   *  - no overflows: d_value < d_modulus
   *  - no negative numbers: d_value >= 0
   */

  FfSize d_size;
  Integer d_value;

}; /* class FiniteFieldValue */

/*
 * Hash function for the FfSize constants.
 */
struct FfSizeHashFunction
{
  size_t operator()(const FfSize& to) const { return to.d_val.hash(); }
}; /* struct FfSizeHashFunction */

/*
 * Hash function for the FiniteFieldValue.
 */
struct FiniteFieldValueHashFunction
{
  size_t operator()(const FiniteFieldValue& ff) const { return ff.hash(); }
}; /* struct FiniteFieldValueHashFunction */

/* -----------------------------------------------------------------------
 ** Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

/* Return true if x is equal to 'y'. */
bool operator==(const FiniteFieldValue& x, const FiniteFieldValue& y);

/* Return true if x is not equal to 'y'. */
bool operator!=(const FiniteFieldValue& x, const FiniteFieldValue& y);

/* Unsigned Inequality --------------------------------------------------- */

/* Return true if x is unsigned less than finite field 'y'. */
bool operator<(const FiniteFieldValue& x, const FiniteFieldValue& y);

/* Return true if x is unsigned less than or equal to finite field 'y'. */
bool operator<=(const FiniteFieldValue& x, const FiniteFieldValue& y);

/* Return true if x is unsigned greater than finite field 'y'. */
bool operator>(const FiniteFieldValue& x, const FiniteFieldValue& y);

/* Return true if x is unsigned greater than or equal to finite field 'y'. */
bool operator>=(const FiniteFieldValue& x, const FiniteFieldValue& y);

/* Arithmetic operations ------------------------------------------------- */

/* Return a finite field representing the addition (x + y). */
FiniteFieldValue operator+(const FiniteFieldValue& x,
                           const FiniteFieldValue& y);

/* Return a finite field representing the subtraction (x - y). */
FiniteFieldValue operator-(const FiniteFieldValue& x,
                           const FiniteFieldValue& y);

/* Return a finite field representing the negation of x. */
FiniteFieldValue operator-(const FiniteFieldValue& x);

/* Return a finite field representing the multiplication (x * y). */
FiniteFieldValue operator*(const FiniteFieldValue& x,
                           const FiniteFieldValue& y);

/* Return a finite field representing the division (x / y). */
FiniteFieldValue operator/(const FiniteFieldValue& x,
                           const FiniteFieldValue& y);

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const FiniteFieldValue& ff);
std::ostream& operator<<(std::ostream& os, const FfSize& ff);

}  // namespace cvc5::internal

#endif /* CVC5__FINITE_FIELDVALUE_H */
