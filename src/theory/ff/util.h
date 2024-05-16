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
#include <exception>
#include <unordered_map>

// internal includes
#include "expr/node.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** A finite field model */
using FfModel = std::unordered_map<Node, FiniteFieldValue>;

/**
 * A class associated with a specific field (for inheritting).
 *
 * A FieldObj is constructed from an FfSize, and provides various helper
 * functions for the field of that size.
 * */
class FieldObj
{
 public:
  FieldObj(const FfSize& size);
  /** create a sum (with as few as 0 elements); accepts Nodes or TNodes */
  template <bool ref_count>
  Node mkAdd(const std::vector<NodeTemplate<ref_count>>& summands);
  /** create a product (with as few as 0 elements); accepts Nodes or TNodes */
  template <bool ref_count>
  Node mkMul(const std::vector<NodeTemplate<ref_count>>& summands);
  /** the one constant in this field */
  const Node& one() const { return d_one; }
  /** the zero constant in this field */
  const Node& zero() const { return d_zero; }
  /** the size of this field */
  const FfSize& size() const { return d_size; }
#ifdef CVC5_USE_COCOA
  /** the CoCoA ring of integers modulo this field's size */
  const CoCoA::ring& coeffRing() const { return d_coeffRing; }
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

/** Testing whether something is related to (any) FF */

/** Is this a field term with non-field kind? */
bool isFfLeaf(const Node& n);
/** Is this a field term? */
bool isFfTerm(const Node& n);
/** Is this a field fact (equality of disequality)? */
bool isFfFact(const Node& n);

/** Used to signal check timeouts */
class FfTimeoutException : public Exception
{
 public:
  FfTimeoutException(const std::string& where);
  ~FfTimeoutException() override;
};
/** Testing whether something is related to (this specific) FF */

/** Is this a (this) field term with non-field kind? */
bool isFfLeaf(const Node& n, const FfSize& field);
/** Is this a (this) field term? */
bool isFfTerm(const Node& n, const FfSize& field);
/** Is this a (this) field fact (equality of disequality)? */
bool isFfFact(const Node& n, const FfSize& field);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__UTIL_H */
