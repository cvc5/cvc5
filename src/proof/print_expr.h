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
 * Utilities for printing expressions in proofs
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PRINT_EXPR_H
#define CVC5__PROOF__PRINT_EXPR_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace proof {

/**
 * A term, type or a proof. This class is used for printing combinations of
 * proofs terms and types.
 */
class PExpr
{
 public:
  PExpr() : d_node(), d_pnode(nullptr), d_typeNode() {}
  PExpr(Node n) : d_node(n), d_pnode(nullptr), d_typeNode() {}
  PExpr(const ProofNode* pn) : d_node(), d_pnode(pn), d_typeNode() {}
  PExpr(TypeNode tn) : d_node(), d_pnode(nullptr), d_typeNode(tn) {}
  ~PExpr() {}
  /** The node, if this p-exression is a node */
  Node d_node;
  /** The proof node, if this p-expression is a proof */
  const ProofNode* d_pnode;
  /** The type node, if this p-expression is a type */
  TypeNode d_typeNode;
};

/**
 * A stream of p-expressions, which appends p-expressions to a reference vector.
 * That vector can then be used when printing a proof.
 */
class PExprStream
{
 public:
  /**
   * Takes a reference to a stream (vector of p-expressions), and the
   * representation true/false (tt/ff).
   */
  PExprStream(std::vector<PExpr>& stream,
              Node tt = Node::null(),
              Node ff = Node::null());
  /** Append a proof node */
  PExprStream& operator<<(const ProofNode* pn);
  /** Append a node */
  PExprStream& operator<<(Node n);
  /** Append a type node */
  PExprStream& operator<<(TypeNode tn);
  /** Append a Boolean */
  PExprStream& operator<<(bool b);
  /** Append a pexpr */
  PExprStream& operator<<(PExpr p);

 private:
  /** Reference to the stream */
  std::vector<PExpr>& d_stream;
  /** Builtin nodes for true and false */
  Node d_tt;
  Node d_ff;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
