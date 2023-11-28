/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of shadow elimination node conversion
 */

#include "expr/elim_shadow_converter.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

/**
 * - QElimShadowAttribute: cached on (q, q', v), which is used to replace a
 * shadowed variable v, which is quantified by a subformula q' of quantified
 * formula q. Shadowed variables may be introduced when e.g. quantified formulas
 * appear on the right hand sides of substitutions in preprocessing. They are
 * eliminated by the rewriter.
 */
struct QElimShadowAttributeId
{
};
using QElimShadowAttribute = expr::Attribute<QElimShadowAttributeId, Node>;

ElimShadowNodeConverter::ElimShadowNodeConverter(const Node& q) : d_closure(q)
{
  Assert(q.isClosure());
  d_vars.insert(d_vars.end(), q[0].begin(), q[0].end());
}

ElimShadowNodeConverter::ElimShadowNodeConverter(
    const Node& n, const std::unordered_set<Node>& vars)
{
  d_closure = n;
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());
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
    if (std::find(d_vars.begin(), d_vars.end(), v) != d_vars.end())
    {
      Node nv = getElimShadowVar(d_closure, n, v);
      oldVars.push_back(v);
      newVars.push_back(nv);
    }
  }
  if (!newVars.empty())
  {
    return n.substitute(
        oldVars.begin(), oldVars.end(), newVars.begin(), newVars.end());
  }
  return n;
}

Node ElimShadowNodeConverter::getElimShadowVar(const Node& q,
                                               const Node& n,
                                               const Node& v)
{
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node cacheVal = BoundVarManager::getCacheValue(q, n, v);
  return bvm->mkBoundVar<QElimShadowAttribute>(cacheVal, v.getType());
}

Node ElimShadowNodeConverter::eliminateShadow(const Node& q)
{
  Assert(q.isClosure());
  ElimShadowNodeConverter esnc(q);
  // eliminate shadowing in all children
  std::vector<Node> children;
  children.push_back(q[0]);
  for (size_t i = 1, nchild = q.getNumChildren(); i < nchild; i++)
  {
    children.push_back(esnc.convert(q[i]));
  }
  return NodeManager::currentNM()->mkNode(q.getKind(), children);
}

}  // namespace cvc5::internal
