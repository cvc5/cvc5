/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace proof {

AletheNodeConverter::AletheNodeConverter() {}

Node AletheNodeConverter::postConvert(Node n)
{
  // whether node is a quantifier with attributes, in which case we remove it
  if (n.getKind() == kind::FORALL && n.getNumChildren() == 3)
  {
    return NodeManager::currentNM()->mkNode(kind::FORALL, n[0], n[1]);
  }
  return n;
}

bool AletheNodeConverter::shouldTraverse(Node n) { return expr::hasClosure(n); }

}  // namespace proof
}  // namespace cvc5::internal
