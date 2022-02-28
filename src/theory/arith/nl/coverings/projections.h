/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements utilities for CAD projection operators.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__CAD_PROJECTIONS_H
#define CVC5__THEORY__ARITH__NL__CAD_PROJECTIONS_H

#ifdef CVC5_USE_POLY

#include <poly/polyxx.h>

#include <vector>

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/**
 * A simple wrapper around std::vector<poly::Polynomial> that ensures that all
 * polynomials are properly factorized and pruned when added to the list.
 */
class PolyVector : public std::vector<poly::Polynomial>
{
 private:
  /** Disable all emplace() */
  void emplace() {}
  /** Disable all emplace_back() */
  void emplace_back() {}
  /** Disable all insert() */
  void insert() {}
  /** Disable all push_back() */
  void push_back() {}

 public:
  PolyVector() {}
  /** Construct from a set of polynomials */
  PolyVector(std::initializer_list<poly::Polynomial> i)
  {
    for (const auto& p : i) add(p);
  }
  /**
   * Adds a polynomial to the list of projection polynomials.
   * Before adding, it factorizes the polynomials and removed constant factors.
   */
  void add(const poly::Polynomial& poly, bool assertMain = false);
  /** Sort and remove duplicates from the list of polynomials. */
  void reduce();
  /** Make this list of polynomials a finest square-free basis. */
  void makeFinestSquareFreeBasis();
  /** Push polynomials with a lower main variable to another PolyVector. */
  void pushDownPolys(PolyVector& down, poly::Variable var);
};

/**
 * Computes McCallum's projection operator.
 */
PolyVector projectionMcCallum(const std::vector<poly::Polynomial>& polys);

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif

#endif
