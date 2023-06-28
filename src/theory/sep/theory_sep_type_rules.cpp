/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

TypeNode SepEmpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SepEmpTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == kind::SEP_EMP);
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
  Assert(n.getKind() == kind::SEP_PTO);
  if (check)
  {
    TypeNode refType = n[0].getType(check);
    TypeNode ptType = n[1].getType(check);
  }
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
  Assert(n.getKind() == kind::SEP_STAR);
  if (check)
  {
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      TypeNode ctype = n[i].getType(check);
      if (ctype != btype)
      {
        throw TypeCheckingExceptionPrivate(n,
                                           "child of sep star is not Boolean");
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
  Assert(n.getKind() == kind::SEP_WAND);
  if (check)
  {
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      TypeNode ctype = n[i].getType(check);
      if (ctype != btype)
      {
        throw TypeCheckingExceptionPrivate(
            n, "child of sep magic wand is not Boolean");
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
  Assert(n.getKind() == kind::SEP_LABEL);
  if (check)
  {
    TypeNode ctype = n[0].getType(check);
    if (ctype != btype)
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "child of sep label is not Boolean");
    }
    TypeNode stype = n[1].getType(check);
    if (!stype.isSet())
    {
      throw TypeCheckingExceptionPrivate(n, "label of sep label is not a set");
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
  Assert(n.getKind() == kind::SEP_NIL);
  Assert(check);
  TypeNode type = n.getType();
  return type;
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal
