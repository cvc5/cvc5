/*********************                                                        */
/*! \file print_expr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF__PRINT_EXPR_H
#define CVC4__PROOF__PRINT_EXPR_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace cvc5 {
namespace proof {

/** A term or a proof */
class PExpr
{
 public:
  PExpr() : d_node(), d_pnode(nullptr), d_typeNode() {}
  PExpr(Node n) : d_node(n), d_pnode(nullptr), d_typeNode() {}
  PExpr(const ProofNode* pn) : d_node(), d_pnode(pn), d_typeNode() {}
  PExpr(TypeNode tn) : d_node(), d_pnode(nullptr), d_typeNode(tn) {}
  ~PExpr() {}
  /** The node */
  Node d_node;
  /** The proof node */
  const ProofNode* d_pnode;
  /** The type node */
  TypeNode d_typeNode;
};

class PExprStream
{
 public:
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
  /** Builtin nodes */
  Node d_tt;
  Node d_ff;
};

}  // namespace proof
}  // namespace cvc5

#endif
