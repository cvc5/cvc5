/*********************                                                        */
/*! \file term_context.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term context
 **/

#include "expr/term_context.h"

namespace CVC4 {

TermContext::TermContext(uint32_t ivalue) : d_initVal(ivalue)
{
  
}
uint32_t TermContext::initialValue()
{
  return d_initVal;
}


RtfTermContext::RtfTermContext() : TermContext(0)
{
  
}

uint32_t RtfTermContext::computeValue(TNode t, uint32_t tval, size_t child)
{
  if (t.isClosure())
  {
    if (tval%2==0)
    {
      tval = tval+1;
    }
  }
  else if (hasNestedTermChildren(t))
  {
    if (tval<2)
    {
      tval + 2;
    }
  }
  return 
}

uint32_t RtfTermContext::getValue(bool inQuant, bool inTerm)
{
  return (inQuant ? 1 : 0) + 2*(inTerm ? 1 : 0);
}

void RtfTermContext::getFlags(uint32_t val, bool& inQuant, bool& inTerm)
{
  inQuant = val%2==1;
  inTerm = val>=2;
}

bool RtfTermContext::hasNestedTermChildren( TNode t ) {
  // dont' worry about FORALL or EXISTS, these are part of inQuant.
  return theory::kindToTheoryId(node.getKind())!=theory::THEORY_BOOL && 
         node.getKind()!=kind::EQUAL && node.getKind()!=kind::SEP_STAR && 
         node.getKind()!=kind::SEP_WAND && node.getKind()!=kind::SEP_LABEL && 
         node.getKind()!=kind::BITVECTOR_EAGER_ATOM;
}


TCtxNode::TCtxNode(Node n, TermContext * tctx) : d_node(n), d_val(val), d_tctx(tctx)
{
}

TCtxNode::TCtxNode(Node n, uint32_t val, TermContext * tctx) : d_node(n), d_val(val), d_tctx(tctx)
{
  
}

size_t TCtxNode::getNumChildren() const
{
  return d_node.getNumChildren();
}

TCtxNode TCtxNode::getChild(size_t i) const
{
  Assert (i<d_node.getNumChildren());
  return TCtxNode(d_node[i], tctx->computeValue(d_node, d_val, i), d_tctx);
}

Node TCtxNode::getNode() const
{
  return d_node;
}

uint32_t TCtxNode::getTermContext() const
{
  return d_val;
}

Node TCtxNode::getNodeHash() const
{
  return computeNodeHash(d_node, d_val);
}

Node TCtxNode::computeNodeHash(Node n, uint32_t val)
{
  return NodeManager::currentNM()->mkNode(SEXPR, n, nm->mkConst(Rational(val)));
}

Node TCtxNode::decomposeNodeHash(Node h, uint32_t& val)
{  
  if (h.getKind()!=SEXPR || h.getNumChildren()!=2)
  {
    Assert(false) << "TermContext::decomposeNodeHash: unexpected node " << h;
    return Node::null();
  }
  Node ival = h[1];
  if (!ival.isConst() || !ival.getType().isInteger()
      || !n.getConst<Rational>().getNumerator().fitsUnsignedInt())
  {
    Assert(false) << "TermContext::decomposeNodeHash: unexpected term context integer in hash " << h;
    return Node::null();
  }
  val = ival.getConst<Rational>().getNumerator().toUnsignedInt();
  return h[0];
}

TCtxStack::TCtxStack(TermContext * tctx) : d_tctx(tctx)
{
}

void TCtxStack::pushInitial(Node t)
{
  Assert (d_stack.empty());
  d_stack.push_back(std::pair<Node, uint32_t>(t, d_tctx->initialValue()));
}

void TCtxStack::pushChildren(Node t, uint32_t tval)
{
  for (size_t i=0, nchild = t.getNumChildren(); i<nchild; i++)
  {
    pushChild(t, tval, i);
  }
}

void TCtxStack::pushChild(Node t, uint32_t tval, size_t index)
{
  Assert (index<t.getNumChildren());
  uint32_t tcval = d_tctx->computeValue(t, tval, index);
  d_stack.push_back(std::pair<Node, uint32_t>(t[index], tcval));
}

void TCtxStack::push(Node t, uint32_t tval)
{
  d_stack.push_back(std::pair<Node, uint32_t>(t, tval));
}

void TCtxStack::pop()
{
  d_stack.pop();
}

void TCtxStack::clear()
{
  d_stack.clear();
}
size_t TCtxStack::size() const
{
  return d_stack.size();
}

bool TCtxStack::empty()
{
  return d_stack.empty();
}

std::pair<Node, uint32_t> TCtxStack::getCurrent() const
{
  return d_stack.back();
}

}  // namespace CVC4
