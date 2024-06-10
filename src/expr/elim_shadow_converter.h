/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of shadow elimination node conversion
 */
#include "cvc5_private.h"

#ifndef CVC5__EXPR__ELIM_SHADOW_NODE_CONVERTER_H
#define CVC5__EXPR__ELIM_SHADOW_NODE_CONVERTER_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {

/**
 * This converts a node into one that does not involve shadowing with the
 * given variables. In particular, if the given vars passed to the constructor
 * are bound in any binder in a subterm of the node to convert, they
 * are replaced by fresh variables.
 *
 * Shadowed variables may be introduced when e.g. quantified formulas
 * appear on the right hand sides of substitutions in preprocessing. They should
 * be eliminated by the rewriter. This utility is the standard method for
 * eliminating them.
 */
class ElimShadowNodeConverter : public NodeConverter
{
 public:
  /**
   * Eliminate shadowing of the top-most variables in closure q.
   */
  ElimShadowNodeConverter(NodeManager* nm, const Node& q);
  /**
   * Eliminate shadowing of variables vars. Node n is a term used as a unique
   * identifier for which the introduced bound variables are indexed on.
   */
  ElimShadowNodeConverter(NodeManager* nm,
                          const Node& n,
                          const std::unordered_set<Node>& vars);
  ~ElimShadowNodeConverter() {}
  /**
   * Convert node n as described above during post-order traversal. This
   * typically should be a subterm of the body of q, assuming that convert
   * was called on the body of q.
   */
  Node postConvert(Node n) override;
  /**
   * Get the bound variable used for eliminating shadowing of the i^th variable
   * bound by closure n that occurs as a subterm of closure q.
   */
  static Node getElimShadowVar(const Node& q, const Node& n, size_t i);

  /**
   * Eliminate shadowing in the closure q. This includes eliminating duplicate
   * variables in the quantifier prefix of q.
   * @param q The term to process which should have a binder kind.
   * @return The result of eliminating shadowing in q.
   */
  static Node eliminateShadow(const Node& q);

 private:
  /** The closure to eliminate shadowing from */
  Node d_closure;
  /** The variables */
  std::vector<Node> d_vars;
};

}  // namespace cvc5::internal

#endif
