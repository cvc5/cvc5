/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of rewriter for the theory of (co)inductive datatypes.
 */

#include "theory/datatypes/theory_datatypes_utils.h"

#include "expr/ascription_type.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {
namespace utils {

Node getSelector(TypeNode dtt,
                 const DTypeConstructor& dc,
                 size_t index,
                 bool shareSel)
{
  return shareSel ? dc.getSharedSelector(dtt, index) : dc.getSelector(index);
}

Node applySelector(const DTypeConstructor& dc,
                   size_t index,
                   bool shareSel,
                   const Node& n)
{
  Node s = getSelector(n.getType(), dc, index, shareSel);
  return NodeManager::currentNM()->mkNode(APPLY_SELECTOR, s, n);
}

Node getInstCons(Node n, const DType& dt, size_t index, bool shareSel)
{
  Assert(index < dt.getNumConstructors());
  std::vector<Node> children;
  NodeManager* nm = NodeManager::currentNM();
  TypeNode tn = n.getType();
  for (size_t i = 0, nargs = dt[index].getNumArgs(); i < nargs; i++)
  {
    Node nc =
        nm->mkNode(APPLY_SELECTOR, getSelector(tn, dt[index], i, shareSel), n);
    children.push_back(nc);
  }
  Node n_ic = mkApplyCons(tn, dt, index, children);
  Assert(n_ic.getType() == tn);
  return n_ic;
}

Node mkApplyCons(TypeNode tn,
                 const DType& dt,
                 size_t index,
                 const std::vector<Node>& children)
{
  Assert(tn.isDatatype());
  Assert(index < dt.getNumConstructors());
  Assert(dt[index].getNumArgs() == children.size());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> cchildren;
  cchildren.push_back(dt[index].getConstructor());
  cchildren.insert(cchildren.end(), children.begin(), children.end());
  if (dt.isParametric())
  {
    // add type ascription for ambiguous constructor types
    Trace("datatypes-parametric")
        << "Constructor is " << dt[index] << std::endl;
    cchildren[0] = dt[index].getInstantiatedConstructor(tn);
  }
  return nm->mkNode(APPLY_CONSTRUCTOR, cchildren);
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
    case TESTER_TYPE:
    case UPDATER_TYPE: return t[0].getDType();
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
}  // namespace cvc5::internal
