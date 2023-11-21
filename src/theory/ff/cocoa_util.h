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
 * CoCoA utilities
 */

#ifdef CVC5_USE_COCOA

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__COCOA_UTIL_H
#define CVC5__THEORY__FF__COCOA_UTIL_H

// external includes
#include <CoCoA/BigInt.H>
#include <CoCoA/ring.H>

// std includes
#include <optional>
#include <sstream>
#include <vector>

// internal includes
#include "util/finite_field_value.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** Type definitions. */

/** A polynomial. (note: C++/Cocoa doesn't distinguish this from Scalar) */
using Poly = CoCoA::RingElem;
/** A coefficient. (note: C++/Cocoa doesn't distinguish this from Poly) */
using Scalar = CoCoA::RingElem;
/** A list of polynomials. */
using Polys = std::vector<Poly>;
/** A partial input (point/vector with optional entries) to a polynomial */
using PartialPoint = std::vector<std::optional<Scalar>>;
/** An input (point/vector) to a polynomial */
using Point = std::vector<Scalar>;

/**
 * partial evaluation of polynomials
 *
 * returns an empty std::optional when some variable in `poly` does not have a
 * value in `values`
 */
std::optional<Scalar> cocoaEval(Poly poly, const PartialPoint& values);

/** total evaluation of polynomials */
Scalar cocoaEval(Poly poly, const Point& values);

/** convert cocoa integer mod p to a FiniteFieldValue. */
FiniteFieldValue cocoaFfToFfVal(const Scalar& elem, const FfSize& size);

/** convert an Integer to CoCoA::BitInt. */
CoCoA::BigInt intToCocoa(const Integer& i);

/** get the string representation of a type that implements operator<<. */
template <typename T>
std::string extractStr(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__COCOA_UTIL_H */

#endif /* CVC5_USE_COCOA */
