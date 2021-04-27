/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of boolean.
 */

#include "theory/booleans/theory_bool_type_rules.h"

#include <sstream>

namespace cvc5 {
namespace theory {
namespace boolean {

TypeNode BooleanTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  TypeNode booleanType = nodeManager->booleanType();
  if (check)
  {
    for (const auto& child : n)
    {
      if (!child.getType(check).isBoolean())
      {
        Debug("pb") << "failed type checking: " << child << std::endl;
        Debug("pb") << "  integer: " << child.getType(check).isInteger()
                    << std::endl;
        Debug("pb") << "  real: " << child.getType(check).isReal() << std::endl;
        throw TypeCheckingExceptionPrivate(n,
                                           "expecting a Boolean subexpression");
      }
    }
  }
  return booleanType;
}

TypeNode IteTypeRule::computeType(NodeManager* nodeManager, TNode n, bool check)
{
  TypeNode thenType = n[1].getType(check);
  TypeNode elseType = n[2].getType(check);
  TypeNode iteType = TypeNode::leastCommonTypeNode(thenType, elseType);
  if (check)
  {
    TypeNode booleanType = nodeManager->booleanType();
    if (n[0].getType(check) != booleanType)
    {
      throw TypeCheckingExceptionPrivate(n, "condition of ITE is not Boolean");
    }
    if (iteType.isNull())
    {
      std::stringstream ss;
      ss << "Both branches of the ITE must be a subtype of a common type."
         << std::endl
         << "then branch: " << n[1] << std::endl
         << "its type   : " << thenType << std::endl
         << "else branch: " << n[2] << std::endl
         << "its type   : " << elseType << std::endl;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return iteType;
}

}  // namespace boolean
}  // namespace theory
}  // namespace cvc5
