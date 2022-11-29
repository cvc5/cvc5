/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields theory type rules.
 */

#include "theory/ff/theory_ff_type_rules.h"

#include "util/cardinality.h"
#include "util/ff_val.h"

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

TypeNode FiniteFieldConstantTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool _check)
{
  return nodeManager->mkFiniteFieldType(
      n.getConst<FfVal>().getFieldSize());
}

TypeNode FiniteFieldFixedFieldTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
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
