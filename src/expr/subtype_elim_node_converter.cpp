/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of subtype elimination node conversion
 */

#include "expr/subtype_elim_node_converter.h"

#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

SubtypeElimNodeConverter::SubtypeElimNodeConverter() {}

bool SubtypeElimNodeConverter::isRealTypeStrict(TypeNode tn)
{
  return tn.isReal();
}

Node SubtypeElimNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  bool convertToRealChildren = false;
  if (k == Kind::ADD || k == Kind::MULT || k == Kind::NONLINEAR_MULT)
  {
    convertToRealChildren = isRealTypeStrict(n.getType());
  }
  else if (k == Kind::GEQ || k == Kind::GT || k == Kind::LEQ || k == Kind::LT)
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
          children.push_back(nm->mkNode(Kind::TO_REAL, nc));
        }
      }
      else
      {
        children.push_back(nc);
      }
    }
    return nm->mkNode(k, children);
  }
  // convert skolems as well, e.g. the purify skolem for (> 1 0.0) becomes the
  // purify skolem for (> 1.0 0.0).
  if (n.isVar())
  {
    SkolemManager* skm = NodeManager::currentNM()->getSkolemManager();
    SkolemId id;
    Node cacheVal;
    if (skm->isSkolemFunction(n, id, cacheVal))
    {
      Node cacheValc = convert(cacheVal);
      if (cacheValc != cacheVal)
      {
        return skm->mkSkolemFunction(id, cacheValc);
      }
    }
  }
  return n;
}

}  // namespace cvc5::internal
