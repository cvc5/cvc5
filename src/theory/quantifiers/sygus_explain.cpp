/*********************                                                        */
/*! \file sygus_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniques for sygus explanations
 **/

#include "theory/quantifiers/sygus_explain.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void TermRecBuild::addTerm(Node n)
{
  d_term.push_back(n);
  std::vector<Node> currc;
  d_kind.push_back(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    currc.push_back(n.getOperator());
    d_has_op.push_back(true);
  }
  else
  {
    d_has_op.push_back(false);
  }
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    currc.push_back(n[i]);
  }
  d_children.push_back(currc);
}

void TermRecBuild::init(Node n)
{
  Assert(d_term.empty());
  addTerm(n);
}

void TermRecBuild::push(unsigned p)
{
  Assert(!d_term.empty());
  unsigned curr = d_term.size() - 1;
  Assert(d_pos.size() == curr);
  Assert(d_pos.size() + 1 == d_children.size());
  Assert(p < d_term[curr].getNumChildren());
  addTerm(d_term[curr][p]);
  d_pos.push_back(p);
}

void TermRecBuild::pop()
{
  Assert(!d_pos.empty());
  d_pos.pop_back();
  d_kind.pop_back();
  d_has_op.pop_back();
  d_children.pop_back();
  d_term.pop_back();
}

void TermRecBuild::replaceChild(unsigned i, Node r)
{
  Assert(!d_term.empty());
  unsigned curr = d_term.size() - 1;
  unsigned o = d_has_op[curr] ? 1 : 0;
  d_children[curr][i + o] = r;
}

Node TermRecBuild::getChild(unsigned i)
{
  unsigned curr = d_term.size() - 1;
  unsigned o = d_has_op[curr] ? 1 : 0;
  return d_children[curr][i + o];
}

Node TermRecBuild::build(unsigned d)
{
  Assert(d_pos.size() + 1 == d_term.size());
  Assert(d < d_term.size());
  int p = d < d_pos.size() ? d_pos[d] : -2;
  std::vector<Node> children;
  unsigned o = d_has_op[d] ? 1 : 0;
  for (unsigned i = 0; i < d_children[d].size(); i++)
  {
    Node nc;
    if (p + o == i)
    {
      nc = build(d + 1);
    }
    else
    {
      nc = d_children[d][i];
    }
    children.push_back(nc);
  }
  return NodeManager::currentNM()->mkNode(d_kind[d], children);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
