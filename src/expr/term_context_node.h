/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term context node utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__TERM_CONTEXT_NODE_H
#define CVC5__EXPR__TERM_CONTEXT_NODE_H

#include "expr/node.h"

namespace cvc5::internal {

class TCtxStack;
class TermContext;

/**
 * A (term-context) sensitive term. This is a wrapper around a Node that
 * additionally has a term context identifier, see getTermContext(). It depends
 * on a pointer to a TermContext callback class (see term_context.h).
 */
class TCtxNode
{
  friend class TCtxStack;

 public:
  TCtxNode(Node n, const TermContext* tctx);
  /** get number of children */
  size_t getNumChildren() const;
  /** get child at index i */
  TCtxNode getChild(size_t i) const;
  /** get node */
  Node getNode() const;
  /** get context */
  uint32_t getContextId() const;
  /** get term context */
  const TermContext* getTermContext() const;
  //---------------------- utility methods
  /**
   * Get node hash, which is a unique node representation of this TCtxNode.
   * This method calls the method below on the data members of this class.
   */
  Node getNodeHash() const;
  /**
   * Get node hash, which is a unique node representation of the pair (n, val).
   * In particular, this returns (SEXPR n (CONST_INTEGER val)).
   */
  static Node computeNodeHash(Node n, uint32_t val);
  /**
   * Decompose node hash, which is an inverse of the above operation. In
   * particular, given input h, this returns a node n and sets val to a value
   * such that computeNodeHash(n, val) returns h.
   */
  static Node decomposeNodeHash(Node h, uint32_t& val);
  //---------------------- end utility methods
 private:
  /** private constructor */
  TCtxNode(Node n, uint32_t val, const TermContext* tctx);
  /** The node */
  Node d_node;
  /** The term context identifier */
  uint32_t d_val;
  /** The term context */
  const TermContext* d_tctx;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */
