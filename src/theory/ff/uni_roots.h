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
 * Root finding for univariate polynomials in prime fields.
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__UNI_ROOTS_H
#define CVC5__THEORY__FF__UNI_ROOTS_H

#include <CoCoA/RingFp.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/ring.H>

#include <vector>

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * Compute a monic polynomial q(X) of minimal degree that has the same real root
 * set as f(X). Thus, q is a product of linear factors.
 *
 * That is, if f has unique factorization
 *
 *    (X - c1)^e1 * (X - c2)^e2 * ... * (X - ck)^ek * q1(X)^e{k+1} * ...
 *
 * where the qi are all super-linear and irreducible, then this function returns
 *
 *    (X - c1) * (X - c2) * ... * (X - ck)
 */
CoCoA::RingElem distinctRootsPoly(CoCoA::RingElem f);

/**
 * Given a univariate f over a finite field, return a list of roots in that
 * field.
 *
 * The list is sorted by string representation.
 */
std::vector<CoCoA::RingElem> roots(CoCoA::RingElem f);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__UNI_ROOTS_H */

#endif /* CVC5_USE_COCOA */
