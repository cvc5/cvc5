/*********************                                                        */
/*! \file theory_builtin_type_rules.cpp
 ** \verbatim
 ** Top contributors (to current version):
 ** Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Type rules for the builtin theory
 **
 ** Type rules for the builtin theory.
 **/

#include "theory/builtin/theory_builtin_type_rules.h"

#include "expr/attribute.h"

namespace CVC4 {
namespace theory {
namespace builtin {

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
  Node k = NodeManager::currentNM()->mkSkolem(
      "groundTerm", type, "a ground term created for type " + type.toString());
  type.setAttribute(gta, k);
  return k;
}

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4
