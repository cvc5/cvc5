/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Expand definitions for floating-point arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__FP_EXPAND_DEFS_H
#define CVC5__THEORY__FP__FP_EXPAND_DEFS_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/trust_node.h"

namespace cvc5::internal {
namespace theory {
namespace fp {

/**
 * Module responsibile for expanding definitions for the FP theory.
 */
class FpExpandDefs
{
  using PairTypeNodeHashFunction = PairHashFunction<TypeNode,
                                                    TypeNode,
                                                    std::hash<TypeNode>,
                                                    std::hash<TypeNode>>;
  /** Uninterpreted functions for undefined cases of non-total operators. */
  using ComparisonUFMap = context::CDHashMap<TypeNode, Node>;
  /** Uninterpreted functions for lazy handling of conversions. */
  using ConversionUFMap = context::
      CDHashMap<std::pair<TypeNode, TypeNode>, Node, PairTypeNodeHashFunction>;

 public:
  FpExpandDefs(NodeManager* nm) : d_nm(nm) {}
  /** expand definitions in node */
  Node expandDefinition(Node node);

 private:
  /**
   * Helper to create a function application on a fresh UF for the undefined
   * zero case of fp.min/fp.max. The UF is instantiated with the operands of
   * the given node.
   * @param node The fp.min/fp.maxnode to create the UF and its application for.
   * @return The function application.
   */
  Node minMaxUF(TNode node);
  /**
   * Helper to create a function application on a fresh UF for the undefined
   * cases of fp.to_ubv/fp.to_sbv. The UF is instantiated with the operands of
   * the given node.
   * @param node The fp.to_sbv/to_ubv node to create the UF and its application
   *             for.
   * @return The function application.
   */
  Node toUbvSbvUF(TNode node);
  /**
   * Helper to create a function application on a fresh UF for the undefined
   * cases of fp.to_real. The UF is instantiated with the operands of the given
   * fp.to_real node.
   * @param node The fp.to_real node to create the UF and its application for.
   * @return The function application.
   */
  Node toRealUF(TNode node);
  /** The associated node manager. */
  NodeManager* d_nm;
}; /* class TheoryFp */

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FP__FP_EXPAND_DEFS_H */
