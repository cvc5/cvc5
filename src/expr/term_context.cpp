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

TermContext::TermContext(uint32_t ivalue) : d_initVal(ivalue) {}
uint32_t TermContext::initialValue() const { return d_initVal; }

RtfTermContext::RtfTermContext() : TermContext(0) {}

uint32_t RtfTermContext::computeValue(TNode t,
                                      uint32_t tval,
                                      size_t child) const
{
  if (t.isClosure())
  {
    if (tval % 2 == 0)
    {
      return tval + 1;
    }
  }
  else if (hasNestedTermChildren(t))
  {
    if (tval < 2)
    {
      return tval + 2;
    }
  }
  return tval;
}

uint32_t RtfTermContext::getValue(bool inQuant, bool inTerm)
{
  return (inQuant ? 1 : 0) + 2 * (inTerm ? 1 : 0);
}

void RtfTermContext::getFlags(uint32_t val, bool& inQuant, bool& inTerm)
{
  inQuant = val % 2 == 1;
  inTerm = val >= 2;
}

bool RtfTermContext::hasNestedTermChildren(TNode t)
{
  Kind k = t.getKind();
  // dont' worry about FORALL or EXISTS, these are part of inQuant.
  return theory::kindToTheoryId(k) != theory::THEORY_BOOL && k != kind::EQUAL
         && k != kind::SEP_STAR && k != kind::SEP_WAND && k != kind::SEP_LABEL
         && k != kind::BITVECTOR_EAGER_ATOM;
}

uint32_t PolarityTermContext::computeValue(TNode t,
                                           uint32_t tval,
                                           size_t index) const
{
  switch (t.getKind())
  {
    case kind::AND:
    case kind::OR:
    case kind::SEP_STAR:
      // polarity preserved
      return tval;
    case kind::IMPLIES:
      // first child reverses, otherwise we preserve
      return index == 0 ? (tval == 0 ? 0 : (3 - tval)) : tval;
    case kind::NOT:
      // polarity reversed
      return tval == 0 ? 0 : (3 - tval);
    case kind::ITE:
      // head has no polarity, branches preserve
      return index == 0 ? 0 : tval;
    case kind::FORALL:
      // body preserves, others have no polarity.
      return index == 1 ? tval : 0;
    default:
      // no polarity
      break;
  }
  return 0;
}

uint32_t PolarityTermContext::getValue(bool hasPol, bool pol)
{
  return hasPol ? (pol ? 2 : 1) : 0;
}

void PolarityTermContext::getFlags(uint32_t val, bool& hasPol, bool& pol)
{
  hasPol = val == 0;
  pol = val == 2;
}

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
  return TCtxNode(d_node[i], d_tctx->computeValue(d_node, d_val, i), d_tctx);
}

Node TCtxNode::getNode() const { return d_node; }

uint32_t TCtxNode::getTermContext() const { return d_val; }

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

TCtxStack::TCtxStack(const TermContext* tctx) : d_tctx(tctx) {}

void TCtxStack::pushInitial(Node t)
{
  Assert(d_stack.empty());
  d_stack.push_back(std::pair<Node, uint32_t>(t, d_tctx->initialValue()));
}

void TCtxStack::pushChildren(Node t, uint32_t tval)
{
  for (size_t i = 0, nchild = t.getNumChildren(); i < nchild; i++)
  {
    pushChild(t, tval, i);
  }
}

void TCtxStack::pushChild(Node t, uint32_t tval, size_t index)
{
  Assert(index < t.getNumChildren());
  uint32_t tcval = d_tctx->computeValue(t, tval, index);
  d_stack.push_back(std::pair<Node, uint32_t>(t[index], tcval));
}

void TCtxStack::push(Node t, uint32_t tval)
{
  d_stack.push_back(std::pair<Node, uint32_t>(t, tval));
}

void TCtxStack::pop() { d_stack.pop_back(); }

void TCtxStack::clear() { d_stack.clear(); }
size_t TCtxStack::size() const { return d_stack.size(); }

bool TCtxStack::empty() const { return d_stack.empty(); }

std::pair<Node, uint32_t> TCtxStack::getCurrent() const
{
  return d_stack.back();
}

}  // namespace CVC4
