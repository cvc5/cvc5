/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type rules for the builtin theory.
 */

#include "theory/builtin/theory_builtin_type_rules.h"

#include "expr/attribute.h"
#include "expr/skolem_manager.h"
#include "expr/uninterpreted_constant.h"
#include "util/cardinality.h"

namespace cvc5 {
namespace theory {
namespace builtin {

TypeNode UninterpretedConstantTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
{
  return n.getConst<UninterpretedConstant>().getType();
}

/**
 * Attribute for caching the ground term for each type. Maps TypeNode to the
 * skolem to return for mkGroundTerm.
 */
struct GroundTermAttributeId
{
};
typedef expr::Attribute<GroundTermAttributeId, Node> GroundTermAttribute;

Node SortProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.getKind() == kind::SORT_TYPE);
  GroundTermAttribute gta;
  if (type.hasAttribute(gta))
  {
    return type.getAttribute(gta);
  }
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node k = sm->mkDummySkolem(
      "groundTerm", type, "a ground term created for type " + type.toString());
  type.setAttribute(gta, k);
  return k;
}

Cardinality FunctionProperties::computeCardinality(TypeNode type)
{
  // Don't assert this; allow other theories to use this cardinality
  // computation.
  //
  // Assert(type.getKind() == kind::FUNCTION_TYPE);

  Cardinality argsCard(1);
  // get the largest cardinality of function arguments/return type
  for (size_t i = 0, i_end = type.getNumChildren() - 1; i < i_end; ++i)
  {
    argsCard *= type[i].getCardinality();
  }

  Cardinality valueCard = type[type.getNumChildren() - 1].getCardinality();

  return valueCard ^ argsCard;
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5
