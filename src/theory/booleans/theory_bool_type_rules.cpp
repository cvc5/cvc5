/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
      if (!child.getType(check).isBoolean())
      {
        Trace("pb") << "failed type checking: " << child << std::endl;
        Trace("pb") << "  integer: " << child.getType(check).isInteger()
                    << std::endl;
        Trace("pb") << "  real: " << child.getType(check).isReal() << std::endl;
        throw TypeCheckingExceptionPrivate(n,
                                           "expecting a Boolean subexpression");
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
  TypeNode thenType = n[1].getType(check);
  if (check)
  {
    TypeNode elseType = n[2].getType(check);
    if (thenType != elseType)
    {
      std::stringstream ss;
      ss << "Branches of the ITE must have the same type." << std::endl
         << "then branch: " << n[1] << std::endl
         << "its type   : " << thenType << std::endl
         << "else branch: " << n[2] << std::endl
         << "its type   : " << elseType << std::endl;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (!n[0].getType(check).isBoolean())
    {
      throw TypeCheckingExceptionPrivate(n, "condition of ITE is not Boolean");
    }
  }
  return thenType;
}

}  // namespace boolean
}  // namespace theory
}  // namespace cvc5::internal
