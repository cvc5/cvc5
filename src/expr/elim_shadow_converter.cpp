/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of annotation elimination node conversion
 */

#include "expr/elim_shadow_converter.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

struct QElimShadowAttributeId
{
};
using QElimShadowAttribute = expr::Attribute<QElimShadowAttributeId, Node>;

ElimShadowNodeConverter::ElimShadowNodeConverter(const Node& q) : d_quant(q){
  Assert (q.isClosure());
  d_vars.insert(d_vars.end(), q[0].begin(), q[0].end());
}

Node ElimShadowNodeConverter::postConvert(Node n)
{
  if (!n.isClosure())
  {
    return n;
  }
  std::vector<Node> oldVars;
  std::vector<Node> newVars;
  for (const Node& v : n[0])
  {
    if (std::find(d_vars.begin(), d_vars.end(), v)!=d_vars.end())
    {
      Node nv = getElimShadowVar(d_quant, n, v);
      oldVars.push_back(v);
      newVars.push_back(nv);
    }
  }
  if (!newVars.empty())
  {
    return n.substitute(oldVars.begin(), oldVars.end(), newVars.begin(), newVars.end());
  }
  return n;
}

Node ElimShadowNodeConverter::getElimShadowVar(const Node& q, const Node& n, const Node& v)
{
  NodeManager * nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node cacheVal = BoundVarManager::getCacheValue(q, n, v);
  return bvm->mkBoundVar<QElimShadowAttribute>(cacheVal, v.getType());
}

}  // namespace cvc5::internal
