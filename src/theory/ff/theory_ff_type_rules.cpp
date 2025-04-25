/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields theory type rules.
 */

#include "theory/ff/theory_ff_type_rules.h"

#include "util/cardinality.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

Cardinality FiniteFieldProperties::computeCardinality(TypeNode type)
{
  Assert(type.isFiniteField());

  Integer size = type.getFfSize();
  Cardinality cardinality = size;
  return cardinality;
}

TypeNode FiniteFieldConstantTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode FiniteFieldConstantTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  return nodeManager->mkFiniteFieldType(
      n.getConst<FiniteFieldValue>().getFieldSize());
}

TypeNode FiniteFieldFixedFieldTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode FiniteFieldFixedFieldTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check,
                                                    std::ostream* errOut)
{
  TypeNode t;
  for (const Node& nc : n)
  {
    TypeNode tc = nc.getType(check);
    if (check)
    {
      if (!tc.isMaybeKind(Kind::FINITE_FIELD_TYPE))
      {
        if (errOut)
        {
          (*errOut) << "expecting finite-field terms";
        }
        return TypeNode::null();
      }
    }
    // if first child
    if (t.isNull())
    {
      t = tc;
      continue;
    }
    t = t.leastUpperBound(tc);
    if (t.isNull())
    {
      if (errOut)
      {
        (*errOut) << "expecting comparable finite-field terms";
      }
      return TypeNode::null();
    }
  }
  // if all arguments are fully abstract, ensure we return the abstract finite
  // field type
  if (t.isFullyAbstract())
  {
    return nodeManager->mkAbstractType(Kind::FINITE_FIELD_TYPE);
  }
  return t;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
