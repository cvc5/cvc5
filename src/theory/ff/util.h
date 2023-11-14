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
 * utilities
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__UTIL_H
#define CVC5__THEORY__FF__UTIL_H

// external includes
#ifdef CVC5_USE_COCOA
#include <CoCoA/ring.H>
#endif /* CVC5_USE_COCOA */

// std includes
#include <unordered_map>

// internal includes
#include "expr/node.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** A finite field model */
using FfModel = std::unordered_map<Node, FiniteFieldValue>;

/** The result of a subsolver. */
enum class Result
{
  SAT,
  UNSAT,
  UNKNOWN,
};

/** A class associated with a specific field (for inheritting). */
class FieldObj
{
 public:
  FieldObj(const FfSize& size);
  /** create a sum (with as few as 0 elements) */
  Node mkAdd(std::vector<Node>&& summands);
  /** create a product (with as few as 0 elements) */
  Node mkMul(std::vector<Node>&& factors);
  const Node& one() { return d_one; }
  const Node& zero() { return d_zero; }
  const FfSize& size() { return d_size; }
#ifdef CVC5_USE_COCOA
  const CoCoA::ring& coeffRing() { return d_coeffRing; }
#endif /* CVC5_USE_COCOA */

 private:
  FfSize d_size;
  NodeManager* d_nm;
  Node d_zero;
  Node d_one;
#ifdef CVC5_USE_COCOA
  CoCoA::ring d_coeffRing;
#endif /* CVC5_USE_COCOA */
};

/** Is this a field term with non-field kind? */
bool isFfLeaf(const Node& n);
/** Is this a field term? */
bool isFfTerm(const Node& n);
/** Is this a field fact (equality of disequality)? */
bool isFfFact(const Node& n);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__UTIL_H */
