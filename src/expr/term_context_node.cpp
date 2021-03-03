/*********************                                                        */
/*! \file term_context_node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term context node utility.
 **/

#include "expr/term_context_node.h"

#include "expr/term_context.h"

namespace CVC4 {

TCtxNode::TCtxNode(Node n, const TermContext* tctx)
    : d_node(n), d_val(tctx->initialValue()), d_tctx(tctx)
{
}

TCtxNode::TCtxNode(Node n, uint32_t val, const TermContext* tctx)
    : d_node(n), d_val(val), d_tctx(tctx)
{
}

size_t TCtxNode::getNumChildren() const { return d_node.getNumChildren(); }

TCtxNode TCtxNode::getChild(size_t i) const
{
  Assert(i < d_node.getNumChildren());
  // we are still computing the same term context, with the given child, where
  // the hash has been updated based on the kind, node, current value and child
  // index.
  return TCtxNode(d_node[i], d_tctx->computeValue(d_node, d_val, i), d_tctx);
}

Node TCtxNode::getNode() const { return d_node; }

uint32_t TCtxNode::getContextId() const { return d_val; }

const TermContext* TCtxNode::getTermContext() const { return d_tctx; }

Node TCtxNode::getNodeHash() const { return computeNodeHash(d_node, d_val); }

Node TCtxNode::computeNodeHash(Node n, uint32_t val)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(kind::SEXPR, n, nm->mkConst(Rational(val)));
}

Node TCtxNode::decomposeNodeHash(Node h, uint32_t& val)
{
  if (h.getKind() != kind::SEXPR || h.getNumChildren() != 2)
  {
    Assert(false) << "TermContext::decomposeNodeHash: unexpected node " << h;
    return Node::null();
  }
  Node ival = h[1];
  if (!ival.isConst() || !ival.getType().isInteger()
      || !ival.getConst<Rational>().getNumerator().fitsUnsignedInt())
  {
    Assert(false) << "TermContext::decomposeNodeHash: unexpected term context "
                     "integer in hash "
                  << h;
    return Node::null();
  }
  val = ival.getConst<Rational>().getNumerator().toUnsignedInt();
  return h[0];
}

}  // namespace CVC4
