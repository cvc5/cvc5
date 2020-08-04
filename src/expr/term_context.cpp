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

TermContext::TermContext(int32_t dvalue) : d_defaultVal(dvalue)
{
  
}

void TermContext::pushInitial(Node t)
{
  Assert (d_stack.empty());
  d_stack.push_back(std::pair<Node, int32_t>(t, d_defaultVal));
}

void TermContext::pushChildren(Node t, int32_t tval)
{
  for (size_t i=0, nchild = t.getNumChildren(); i<nchild; i++)
  {
    pushChild(t, tval, i);
  }
}

void TermContext::pushChild(Node t, int32_t tval, size_t index)
{
  Assert (index<t.getNumChildren());
  int32_t tcval = computePushValue(t, tval, index);
  d_stack.push_back(std::pair<Node, int32_t>(t[index], tcval));
}

void TermContext::push(Node t, int32_t tval)
{
  d_stack.push_back(std::pair<Node, int32_t>(t, tval));
}

void TermContext::pop()
{
  d_stack.pop();
}

void TermContext::clear()
{
  d_stack.clear();
}
size_t TermContext::size() const
{
  return d_stack.size();
}

bool TermContext::empty()
{
  return d_stack.empty();
}

std::pair<Node, int32_t> TermContext::getCurrent() const
{
  return d_stack.back();
}

RtfTermContext::RtfTermContext() : TermContext(0)
{
  
}

int32_t RtfTermContext::computePushValue(TNode t, int32_t tval, size_t child)
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

bool RtfTermContext::inQuant() const
{
  int32_t val = d_stack.back().first
  return val%2==1;
}

bool RtfTermContext::inTerm() const
{
  int32_t val = d_stack.back().first
  return val>=2;
}

int32_t RtfTermContext::getValue(bool inQuant, bool inTerm)
{
  return (inQuant ? 1 : 0) + 2*(inTerm ? 1 : 0);
}

void RtfTermContext::getFlags(int32_t val, bool& inQuant, bool& inTerm)
{
  inQuant = val%2==1;
  inTerm = val>=2;
}

bool RtfTermContext::hasNestedTermChildren( TNode t ) {
  // dont' worry about FORALL or EXISTS (handled separately)
  return theory::kindToTheoryId(node.getKind())!=theory::THEORY_BOOL && 
         node.getKind()!=kind::EQUAL && node.getKind()!=kind::SEP_STAR && 
         node.getKind()!=kind::SEP_WAND && node.getKind()!=kind::SEP_LABEL && 
         node.getKind()!=kind::BITVECTOR_EAGER_ATOM;
}


}  // namespace CVC4
