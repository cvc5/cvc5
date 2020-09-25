/*********************                                                        */
/*! \file theory_datatypes_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewriter for the theory of (co)inductive datatypes.
 **
 ** Implementation of rewriter for the theory of (co)inductive datatypes.
 **/

#include "theory/datatypes/theory_datatypes_utils.h"

#include "expr/dtype.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {
namespace utils {

/** get instantiate cons */
Node getInstCons(Node n, const DType& dt, int index)
{
  Assert(index >= 0 && index < (int)dt.getNumConstructors());
  std::vector<Node> children;
  NodeManager* nm = NodeManager::currentNM();
  children.push_back(dt[index].getConstructor());
  TypeNode tn = n.getType();
  for (unsigned i = 0, nargs = dt[index].getNumArgs(); i < nargs; i++)
  {
    Node nc = nm->mkNode(
        APPLY_SELECTOR_TOTAL, dt[index].getSelectorInternal(tn, i), n);
    children.push_back(nc);
  }
  Node n_ic = nm->mkNode(APPLY_CONSTRUCTOR, children);
  if (dt.isParametric())
  {
    // add type ascription for ambiguous constructor types
    if (!n_ic.getType().isComparableTo(tn))
    {
      Debug("datatypes-parametric")
          << "DtInstantiate: ambiguous type for " << n_ic << ", ascribe to "
          << n.getType() << std::endl;
      Debug("datatypes-parametric")
          << "Constructor is " << dt[index] << std::endl;
      TypeNode tspec = dt[index].getSpecializedConstructorType(n.getType());
      Debug("datatypes-parametric")
          << "Type specification is " << tspec << std::endl;
      children[0] = nm->mkNode(APPLY_TYPE_ASCRIPTION,
                               nm->mkConst(AscriptionType(tspec.toType())),
                               children[0]);
      n_ic = nm->mkNode(APPLY_CONSTRUCTOR, children);
      Assert(n_ic.getType() == tn);
    }
  }
  Assert(isInstCons(n, n_ic, dt) == index);
  // n_ic = Rewriter::rewrite( n_ic );
  return n_ic;
}

int isInstCons(Node t, Node n, const DType& dt)
{
  if (n.getKind() == APPLY_CONSTRUCTOR)
  {
    int index = indexOf(n.getOperator());
    const DTypeConstructor& c = dt[index];
    TypeNode tn = n.getType();
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      if (n[i].getKind() != APPLY_SELECTOR_TOTAL
          || n[i].getOperator() != c.getSelectorInternal(tn, i) || n[i][0] != t)
      {
        return -1;
      }
    }
    return index;
  }
  return -1;
}

int isTester(Node n, Node& a)
{
  if (n.getKind() == APPLY_TESTER)
  {
    a = n[0];
    return indexOf(n.getOperator());
  }
  return -1;
}

int isTester(Node n)
{
  if (n.getKind() == APPLY_TESTER)
  {
    return indexOf(n.getOperator());
  }
  return -1;
}

size_t indexOf(Node n) { return DType::indexOf(n); }

size_t cindexOf(Node n) { return DType::cindexOf(n); }

const DType& datatypeOf(Node n)
{
  TypeNode t = n.getType();
  switch (t.getKind())
  {
    case CONSTRUCTOR_TYPE: return t[t.getNumChildren() - 1].getDType();
    case SELECTOR_TYPE:
    case TESTER_TYPE: return t[0].getDType();
    default:
      Unhandled() << "arg must be a datatype constructor, selector, or tester";
  }
}

Node mkTester(Node n, int i, const DType& dt)
{
  return NodeManager::currentNM()->mkNode(APPLY_TESTER, dt[i].getTester(), n);
}

Node mkSplit(Node n, const DType& dt)
{
  std::vector<Node> splits;
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node test = mkTester(n, i, dt);
    splits.push_back(test);
  }
  NodeManager* nm = NodeManager::currentNM();
  return splits.size() == 1 ? splits[0] : nm->mkNode(OR, splits);
}

bool isNullaryApplyConstructor(Node n)
{
  Assert(n.getKind() == APPLY_CONSTRUCTOR);
  for (const Node& nc : n)
  {
    if (nc.getType().isDatatype())
    {
      return false;
    }
  }
  return true;
}

bool isNullaryConstructor(const DTypeConstructor& c)
{
  for (unsigned j = 0, nargs = c.getNumArgs(); j < nargs; j++)
  {
    if (c[j].getType().getRangeType().isDatatype())
    {
      return false;
    }
  }
  return true;
}

bool checkClash(Node n1, Node n2, std::vector<Node>& rew)
{
  Trace("datatypes-rewrite-debug")
      << "Check clash : " << n1 << " " << n2 << std::endl;
  if (n1.getKind() == APPLY_CONSTRUCTOR && n2.getKind() == APPLY_CONSTRUCTOR)
  {
    if (n1.getOperator() != n2.getOperator())
    {
      Trace("datatypes-rewrite-debug")
          << "Clash operators : " << n1 << " " << n2 << " " << n1.getOperator()
          << " " << n2.getOperator() << std::endl;
      return true;
    }
    Assert(n1.getNumChildren() == n2.getNumChildren());
    for (unsigned i = 0, size = n1.getNumChildren(); i < size; i++)
    {
      if (checkClash(n1[i], n2[i], rew))
      {
        return true;
      }
    }
  }
  else if (n1 != n2)
  {
    if (n1.isConst() && n2.isConst())
    {
      Trace("datatypes-rewrite-debug")
          << "Clash constants : " << n1 << " " << n2 << std::endl;
      return true;
    }
    else
    {
      Node eq = NodeManager::currentNM()->mkNode(EQUAL, n1, n2);
      rew.push_back(eq);
    }
  }
  return false;
}

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
