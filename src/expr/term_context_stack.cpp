/*********************                                                        */
/*! \file term_context_stack.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term context stack
 **/

#include "expr/term_context_stack.h"

namespace CVC4 {

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
  Trace("tctx-debug") << "TCtxStack::pushChild: computing " << t << "[" << index
                      << "] / " << tval << std::endl;
  uint32_t tcval = d_tctx->computeValue(t, tval, index);
  Trace("tctx-debug") << "TCtxStack::pushChild: returned " << t << "[" << index
                      << "] / " << tval << " ---> " << tcval << std::endl;
  d_stack.push_back(std::pair<Node, uint32_t>(t[index], tcval));
}

void TCtxStack::pushOp(Node t, uint32_t tval)
{
  Assert(t.hasOperator());
  uint32_t toval = d_tctx->computeValueOp(t, tval);
  d_stack.push_back(std::pair<Node, uint32_t>(t.getOperator(), toval));
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

TCtxNode TCtxStack::getCurrentNode() const
{
  std::pair<Node, uint32_t> curr = TCtxStack::getCurrent();
  return TCtxNode(curr.first, curr.second, d_tctx);
}

}  // namespace CVC4
