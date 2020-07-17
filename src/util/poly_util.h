/*********************                                                        */
/*! \file poly_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for working with LibPoly.
 **
 ** Utilities for working with LibPoly.
 **/

#include "cvc4_private.h"

#ifndef CVC4__POLY_UTIL_H
#define CVC4__POLY_UTIL_H


#include <vector>

#include "maybe.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP

#include <poly/polyxx.h>

namespace CVC4 {
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

/** Converts a poly::Integer to a CVC4::Integer. */
Integer toInteger(const poly::Integer& i);
/** Converts a poly::Integer to a CVC4::Rational. */
Rational toRational(const poly::Integer& r);
/** Converts a poly::Rational to a CVC4::Rational. */
Rational toRational(const poly::Rational& r);
/** Converts a poly::DyadicRational to a CVC4::Rational. */
Rational toRational(const poly::DyadicRational& dr);

/** Converts a CVC4::Integer to a poly::Integer. */
poly::Integer toInteger(const Integer& i);
/** Converts a vector of CVC4::Integers to a vector of poly::Integers. */
std::vector<poly::Integer> toInteger(const std::vector<Integer>& vi);
/** Converts a CVC4::Rational to a poly::Rational. */
poly::Rational toRational(const Rational& r);
/**
 * Converts a CVC4::Rational to a poly::DyadicRational. If the input is not
 * dyadic, no result is produced.
 */
Maybe<poly::DyadicRational> toDyadicRational(const Rational& r);
/**
 * Converts a poly::Rational to a poly::DyadicRational. If the input is not
 * dyadic, no result is produced.
 */
Maybe<poly::DyadicRational> toDyadicRational(const poly::Rational& r);

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
 * CVC4::Rational bounds. As a poly::AlgebraicNumber works on
 * poly::DyadicRationals internally, the bounds are iteratively refined using
 * approximateToDyadic until the respective interval is isolating. If the
 * provided rational bounds are already dyadic, the refinement is skipped.
 */
poly::AlgebraicNumber toPolyRanWithRefinement(poly::UPolynomial&& p,
                                              const Rational& lower,
                                              const Rational& upper);

/**
 * Constructs a CVC4::RealAlgebraicNumber, simply wrapping
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
  /** Sum of degrees of this variable. */
  std::size_t sum_degree = 0;
  /** Number of terms that contain this variable. */
  std::size_t num_terms = 0;
};

void getVariableInformation(VariableInformation& vi,
                            const poly::Polynomial& poly);

}  // namespace poly_utils
}  // namespace CVC4

#endif

#endif /* CVC4__POLY_UTIL_H */
