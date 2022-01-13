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
#include "util/uninterpreted_sort_value.h"

namespace cvc5 {
namespace theory {
namespace builtin {

TypeNode UninterpretedSortValueTypeRule::computeType(NodeManager* nodeManager,
                                                     TNode n,
                                                     bool check)
{
  return n.getConst<UninterpretedSortValue>().getType();
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
  // we typically use this method for sorts, although there are other types
  // where it is used as well, e.g. arrays that are not closed enumerable.
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

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5
