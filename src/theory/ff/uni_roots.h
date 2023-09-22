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

#include <CoCoA/ring.H>
#include <CoCoA/RingFp.H>
#include <CoCoA/SparsePolyRing.H>

#include <vector>

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * Given a univariate f over a finite field, return the monic polynomial with
 * the same base-field roots as f, of minimal degree.
 *
 * Thus, the return is a polynomial with unique linear factors
 */
CoCoA::RingElem distinctRootsPoly(CoCoA::RingElem f);

/**
 * Given a univariate f over a finite field, return a list of roots in that field.
 *
 * The list is sorted.
 */
std::vector<CoCoA::RingElem> roots(CoCoA::RingElem f);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__UNI_ROOTS_H */

#endif /* CVC5_USE_COCOA */
