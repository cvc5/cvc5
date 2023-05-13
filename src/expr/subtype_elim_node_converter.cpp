/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of subtype elimination node conversion
 */

#include "expr/subtype_elim_node_converter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

SubtypeElimNodeConverter::SubtypeElimNodeConverter() {}

bool SubtypeElimNodeConverter::isRealTypeStrict(TypeNode tn)
{
  return tn.isReal() && !tn.isInteger();
}

Node SubtypeElimNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  bool convertToRealChildren = false;
  if (k == ADD || k == MULT || k == NONLINEAR_MULT)
  {
    convertToRealChildren = isRealTypeStrict(n.getType());
  }
  else if (k == GEQ || k == GT || k == LEQ || k == LT)
  {
    convertToRealChildren =
        isRealTypeStrict(n[0].getType()) || isRealTypeStrict(n[1].getType());
  }
  // note that EQUAL is strictly typed so we don't need to handle it here
  if (convertToRealChildren)
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> children;
    for (const Node& nc : n)
    {
      if (nc.getType().isInteger())
      {
        if (nc.isConst())
        {
          // we convert constant integers to constant reals
          children.push_back(nm->mkConstReal(nc.getConst<Rational>()));
        }
        else
        {
          // otherwise, use TO_REAL
          children.push_back(nm->mkNode(TO_REAL, nc));
        }
      }
      else
      {
        children.push_back(nc);
      }
    }
    return nm->mkNode(k, children);
  }
  return n;
}

}  // namespace cvc5::internal
