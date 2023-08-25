/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generic utility to convert between libpoly polynomials and CoCoALib
 * polynomials.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__COCOA_CONVERTER_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__COCOA_CONVERTER_H

#ifdef CVC5_POLY_IMP
#ifdef CVC5_USE_COCOA

#include <CoCoA/library.H>
#include <poly/polyxx.h>

#include <memory>

#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

/**
 * This class implements a generic converter utility between libpoly polynomials
 * and CoCoA polynomials.
 */
class CoCoAConverter
{
 public:
  /** Add mapping from libpoly variable to a CoCoA variable */
  void addVar(const poly::Variable& pv, const CoCoA::RingElem& cv)
  {
    d_varPC.emplace(pv, cv);
  }
  /**
   * Add mapping from a CoCoA variable, identified by its ring id and the
   * indet identifier, to a libpoly polynomial.
   */
  void addVar(const std::pair<long, size_t>& cv, const poly::Variable& pv)
  {
    d_varCP.emplace(cv, pv);
  }

  /**
   * Converts a libpoly integer to a CoCoA::BigInt.
   */
  CoCoA::BigInt operator()(const poly::Integer& i) const
  {
    return CoCoA::BigIntFromMPZ(poly::detail::cast_to_gmp(&i)->get_mpz_t());
  }
  /**
   * Converts a libpoly dyadic rational to a CoCoA::BigRat.
   */
  CoCoA::BigRat operator()(const poly::DyadicRational& dr) const
  {
    return CoCoA::BigRat((*this)(poly::numerator(dr)),
                         (*this)(poly::denominator(dr)));
  }
  /**
   * Converts a libpoly rational to a CoCoA::BigRat.
   */
  CoCoA::BigRat operator()(const poly::Rational& r) const
  {
    return CoCoA::BigRatFromMPQ(poly::detail::cast_to_gmp(&r)->get_mpq_t());
  }
  /**
   * Converts a univariate libpoly polynomial p in variable var to a CoCoA
   * polynomial in the given CoCoA ring.
   */
  CoCoA::RingElem operator()(const poly::UPolynomial& p,
                             const poly::Variable& var,
                             const CoCoA::ring& ring) const;

  /**
   * Converts a libpoly polynomial p in variable var to a CoCoA polynomial in
   * the given CoCoA ring.
   */
  CoCoA::RingElem operator()(const poly::Polynomial& q,
                             const CoCoA::ring& ring) const;

  /**
   * Converts a CoCoA polynomial to a libpoly polynomial.
   */
  poly::Polynomial operator()(const CoCoA::RingElem& p) const
  {
    poly::Integer denom;
    return convertImpl(p, denom);
  }

 private:

  /** Helper class for the conversion of a libpoly polynomial to CoCoA. */
  struct CoCoAPolyConstructor
  {
    const CoCoAConverter& d_state;
    const CoCoA::ring& d_ring;
    CoCoA::RingElem d_result;
  };
  /** Helper method for the conversion of a CoCoA polynomial to libpoly */
  poly::Polynomial convertImpl(const CoCoA::RingElem& p,
                               poly::Integer& denominator) const;

  /**
   * Maps libpoly variables to indets in CoCoA.
   */
  std::map<poly::Variable, CoCoA::RingElem> d_varPC;

  /**
   * Maps CoCoA variables (identified by ring id and indet id) to libpoly
   * variables.
   */
  std::map<std::pair<long, size_t>, poly::Variable> d_varCP;
};

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
#endif
#endif
