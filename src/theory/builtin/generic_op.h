/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for representing generic operators.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__BUILTIN__GENERIC_OP_H
#define CVC5__THEORY__BUILTIN__GENERIC_OP_H

#include <vector>

#include "expr/kind.h"
#include "expr/node.h"

namespace cvc5::internal {

/**
 * The payload for abstract types, which carries a kind specifying the kind
 * of type this abstract type abstracts.
 */
class GenericOp
{
 public:
  GenericOp(Kind k);
  GenericOp(const GenericOp& op);

  /** Return the kind of indexed operator this operator represents */
  Kind getKind() const;

  bool operator==(const GenericOp& op) const;

  /** Is k a kind that is an indexed operator? */
  static bool isIndexedOperatorKind(Kind k);
  /**
   * Return the list of nodes corresponding to the indices of n, which is
   * an operator for an application of kind k.
   */
  static std::vector<Node> getIndicesForOperator(Kind k, Node n);
  /**
   * Return the operator of kind k whose indices are the constants in the
   * given vector.
   */
  static Node getOperatorForIndices(Kind k, const std::vector<Node>& indices);
  /**
   * Get the concrete term corresponding to the application of
   * APPLY_INDEXED_SYMBOLIC. Requires all indices to be constant.
   */
  static Node getConcreteApp(const Node& app);

 private:
  GenericOp();
  /** The kind of indexed operator this operator represents */
  Kind d_kind;
  /** Is k a kind that is an indexed operator? */
  static bool isNumeralIndexedOperatorKind(Kind k);
};

std::ostream& operator<<(std::ostream& out, const GenericOp& op);

/**
 * Hash function for the GenericOp objects.
 */
struct GenericOpHashFunction
{
  size_t operator()(const GenericOp& op) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__GENERIC_OP_H */
