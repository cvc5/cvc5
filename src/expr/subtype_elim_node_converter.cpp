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
 * Implementation of subtype elimination node conversion
 */

#include "expr/subtype_elim_node_converter.h"

using namespace cvc5::kind;

namespace cvc5 {

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
  else if (k == EQUAL || k == GEQ)
  {
    convertToRealChildren =
        isRealTypeStrict(n[0].getType()) || isRealTypeStrict(n[1].getType());
  }
  if (convertToRealChildren)
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> children;
    for (const Node& nc : n)
    {
      if (nc.getType().isInteger())
      {
        // we use CAST_TO_REAL for constants, so that e.g. 5 is printed as
        // 5.0 not (to_real 5)
        Kind nk = nc.isConst() ? CAST_TO_REAL : TO_REAL;
        children.push_back(nm->mkNode(nk, nc));
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

}  // namespace cvc5
