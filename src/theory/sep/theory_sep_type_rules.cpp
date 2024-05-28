/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of sep.
 */

#include "theory/sep/theory_sep_type_rules.h"

namespace cvc5::internal {
namespace theory {
namespace sep {

bool isMaybeBoolean(const TypeNode& tn)
{
  return tn.isBoolean() || tn.isFullyAbstract();
}

TypeNode SepEmpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SepEmpTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SEP_EMP);
  return nodeManager->booleanType();
}

TypeNode SepPtoTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SepPtoTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SEP_PTO);
  return nodeManager->booleanType();
}

TypeNode SepStarTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SepStarTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  TypeNode btype = nodeManager->booleanType();
  Assert(n.getKind() == Kind::SEP_STAR);
  if (check)
  {
    for (const Node& nc : n)
    {
      TypeNode ctype = nc.getTypeOrNull();
      if (!isMaybeBoolean(ctype))
      {
        if (errOut)
        {
          (*errOut) << "child of sep star is not Boolean";
        }
        return TypeNode::null();
      }
    }
  }
  return btype;
}

TypeNode SepWandTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SepWandTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  TypeNode btype = nodeManager->booleanType();
  Assert(n.getKind() == Kind::SEP_WAND);
  if (check)
  {
    for (const Node& nc : n)
    {
      TypeNode ctype = nc.getTypeOrNull();
      if (!isMaybeBoolean(ctype))
      {
        if (errOut)
        {
          (*errOut) << "child of sep magic wand is not Boolean";
        }
        return TypeNode::null();
      }
    }
  }
  return btype;
}

TypeNode SepLabelTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SepLabelTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  TypeNode btype = nodeManager->booleanType();
  Assert(n.getKind() == Kind::SEP_LABEL);
  if (check)
  {
    TypeNode ctype = n[0].getTypeOrNull();
    if (!isMaybeBoolean(ctype))
    {
      if (errOut)
      {
        (*errOut) << "child of sep label is not Boolean";
      }
      return TypeNode::null();
    }
    TypeNode stype = n[1].getTypeOrNull();
    if (!stype.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "label of sep label is not a set";
      }
      return TypeNode::null();
    }
  }
  return btype;
}

TypeNode SepNilTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SepNilTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SEP_NIL);
  Assert(check);
  TypeNode type = n.getTypeOrNull();
  return type;
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal
