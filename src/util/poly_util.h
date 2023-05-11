/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for working with LibPoly.
 */

#include "cvc5_private.h"

#ifndef CVC5__POLY_UTIL_H
#define CVC5__POLY_UTIL_H

#include <optional>
#include <vector>

#include "util/integer.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

namespace cvc5::internal {
/**
 * Utilities for working with libpoly.
 * This namespace contains various basic conversion routines necessary for the
 * integration of LibPoly. Firstly, LibPoly is based on GMP and hence we need
 * conversion from and to CLN (in case CLN is enabled). Otherwise, conversion of
 * number types mostly reduces to simple type casts.
 * Furthermore, conversions between poly::Rational and poly::DyadicRational and
 * constructors for algebraic numbers that need initial refinement of the
 * interval are provided.
 */
namespace poly_utils {

/** Converts a poly::Integer to a cvc5::internal::Integer. */
Integer toInteger(const poly::Integer& i);
/** Converts a poly::Integer to a cvc5::internal::Rational. */
Rational toRational(const poly::Integer& r);
/** Converts a poly::Rational to a cvc5::internal::Rational. */
Rational toRational(const poly::Rational& r);
/** Converts a poly::DyadicRational to a cvc5::internal::Rational. */
Rational toRational(const poly::DyadicRational& dr);

/** Converts a poly::Value to a cvc5::internal::Rational (that may be a bit above). */
Rational toRationalAbove(const poly::Value& v);
/** Converts a poly::Value to a cvc5::internal::Rational (that may be a bit below). */
Rational toRationalBelow(const poly::Value& v);

/** Converts a cvc5::internal::Integer to a poly::Integer. */
poly::Integer toInteger(const Integer& i);
/** Converts a vector of cvc5::internal::Integers to a vector of poly::Integers. */
std::vector<poly::Integer> toInteger(const std::vector<Integer>& vi);
/** Converts a cvc5::internal::Rational to a poly::Rational. */
poly::Rational toRational(const Rational& r);
/**
 * Converts a cvc5::internal::Rational to a poly::DyadicRational. If the input is not
 * dyadic, no result is produced.
 */
std::optional<poly::DyadicRational> toDyadicRational(const Rational& r);
/**
 * Converts a poly::Rational to a poly::DyadicRational. If the input is not
 * dyadic, no result is produced.
 */
std::optional<poly::DyadicRational> toDyadicRational(const poly::Rational& r);

/**
 * Iteratively approximates a poly::Rational by a dyadic poly::Rational.
 * Assuming that r is dyadic, makes one refinement step to move r closer to
 * original.
 * Assumes one starts with lower(original) or ceil(original) for r.
 */
poly::Rational approximateToDyadic(const poly::Rational& r,
                                   const poly::Rational& original);

/**
 * Constructs a poly::AlgebraicNumber, allowing for refinement of the
 * cvc5::internal::Rational bounds. As a poly::AlgebraicNumber works on
 * poly::DyadicRationals internally, the bounds are iteratively refined using
 * approximateToDyadic until the respective interval is isolating. If the
 * provided rational bounds are already dyadic, the refinement is skipped.
 */
poly::AlgebraicNumber toPolyRanWithRefinement(poly::UPolynomial&& p,
                                              const Rational& lower,
                                              const Rational& upper);

/**
 * Constructs a cvc5::internal::RealAlgebraicNumber, simply wrapping
 * toPolyRanWithRefinement.
 */
RealAlgebraicNumber toRanWithRefinement(poly::UPolynomial&& p,
                                        const Rational& lower,
                                        const Rational& upper);

std::size_t totalDegree(const poly::Polynomial& p);

/**
 * Collects information about a single variable in a set of polynomials.
 * Used for determining a variable ordering.
 */
struct VariableInformation
{
  poly::Variable var;
  /** Maximum degree of this variable. */
  std::size_t max_degree = 0;
  /** Maximum degree of the leading coefficient of this variable. */
  std::size_t max_lc_degree = 0;
  /** Maximum of total degrees of terms that contain this variable. */
  std::size_t max_terms_tdegree = 0;
  /** Sum of degrees of this variable within all terms. */
  std::size_t sum_term_degree = 0;
  /** Sum of degrees of this variable within all polynomials. */
  std::size_t sum_poly_degree = 0;
  /** Number of polynomials that contain this variable. */
  std::size_t num_polynomials = 0;
  /** Number of terms that contain this variable. */
  std::size_t num_terms = 0;
};
std::ostream& operator<<(std::ostream& os, const VariableInformation& vi);

void getVariableInformation(VariableInformation& vi,
                            const poly::Polynomial& poly);

}  // namespace poly_utils
}  // namespace cvc5::internal

#endif

#endif /* CVC5__POLY_UTIL_H */
