/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

// std includes
#include <unordered_map>
#include <variant>
#include <vector>

// internal includes
#include "expr/node.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** A finite field model */
using FfModel = std::unordered_map<Node, FiniteFieldValue>;
/** A finite field conflict core */
using FfCore = std::vector<Node>;
/** Indicates an unknown result in FfResult. */
using FfUnknown = std::monostate;
/** The result of a subprocedure: either unknown, a model, or a conflict core */
using FfResult = std::variant<FfUnknown, FfModel, FfCore>;

/**
 * A class associated with a specific field (for inheritting).
 *
 * A FieldObj is constructed from an FfSize, and provides various helper
 * functions for the field of that size.
 * */
class FieldObj
{
 public:
  FieldObj(NodeManager* nm, FfSize  size);
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

 private:
  FfSize d_size;
  NodeManager* d_nm;
  Node d_zero;
  Node d_one;
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
  explicit FfTimeoutException(const std::string& where);
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
