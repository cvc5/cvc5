/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Martin Brain, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  FpExpandDefs(context::UserContext* u);
  /** expand definitions in node */
  TrustNode expandDefinition(Node node);

 private:
  /** TODO: document (projects issue #265) */
  Node minUF(Node);
  Node maxUF(Node);
  Node toUBVUF(Node);
  Node toSBVUF(Node);
  Node toRealUF(Node);
  Node abstractRealToFloat(Node);
  Node abstractFloatToReal(Node);
  ComparisonUFMap d_minMap;
  ComparisonUFMap d_maxMap;
  ConversionUFMap d_toUBVMap;
  ConversionUFMap d_toSBVMap;
  ComparisonUFMap d_toRealMap;
}; /* class TheoryFp */

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FP__THEORY_FP_H */
