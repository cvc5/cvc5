/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of boolean.
 */

#include "theory/booleans/theory_bool_type_rules.h"

#include <sstream>

namespace cvc5::internal {
namespace theory {
namespace boolean {

bool isMaybeBoolean(const TypeNode& tn)
{
  return tn.isBoolean() || tn.isFullyAbstract();
}

TypeNode BooleanTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode BooleanTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  TypeNode booleanType = nodeManager->booleanType();
  if (check)
  {
    for (const auto& child : n)
    {
      TypeNode tc = child.getTypeOrNull();
      if (!isMaybeBoolean(tc))
      {
        if (errOut)
        {
          (*errOut) << "expecting a Boolean subexpression";
        }
        return TypeNode::null();
      }
    }
  }
  return booleanType;
}

TypeNode IteTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode IteTypeRule::computeType(NodeManager* nodeManager,
                                  TNode n,
                                  bool check,
                                  std::ostream* errOut)
{
  TypeNode thenType = n[1].getTypeOrNull();
  TypeNode elseType = n[2].getTypeOrNull();
  TypeNode resType = thenType.leastUpperBound(elseType);
  if (resType.isNull())
  {
    if (errOut)
    {
      (*errOut) << "Branches of the ITE must have comparable type." << std::endl
                << "then branch: " << n[1] << std::endl
                << "its type   : " << thenType << std::endl
                << "else branch: " << n[2] << std::endl
                << "its type   : " << elseType << std::endl;
    }
    return TypeNode::null();
  }
  if (check)
  {
    TypeNode condType = n[0].getTypeOrNull();
    TypeNode booleanType = nodeManager->booleanType();
    if (!isMaybeBoolean(condType))
    {
      if (errOut)
      {
        (*errOut) << "condition of ITE is not Boolean";
      }
      return TypeNode::null();
    }
  }
  return resType;
}

}  // namespace boolean
}  // namespace theory
}  // namespace cvc5::internal
