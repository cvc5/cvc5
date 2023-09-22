/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  TNode::iterator it = n.begin();
  TypeNode t = (*it).getType(check);
  if (check)
  {
    if (t.getKind() != kind::FINITE_FIELD_TYPE)
    {
      throw TypeCheckingExceptionPrivate(n, "expecting finite-field terms");
    }
    TNode::iterator it_end = n.end();
    for (++it; it != it_end; ++it)
    {
      if ((*it).getType(check) != t)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting finite-field terms from the same field");
      }
    }
  }
  return t;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
