/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "util/rational.h"

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

ElimShadowNodeConverter::ElimShadowNodeConverter(NodeManager* nm, const Node& q)
    : NodeConverter(nm), d_closure(q)
{
  Assert(q.isClosure());
  d_vars.insert(d_vars.end(), q[0].begin(), q[0].end());
}

ElimShadowNodeConverter::ElimShadowNodeConverter(
    NodeManager* nm, const Node& n, const std::unordered_set<Node>& vars)
    : NodeConverter(nm)
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
  for (size_t i = 0, nvars = n[0].getNumChildren(); i < nvars; i++)
  {
    const Node& v = n[0][i];
    if (std::find(d_vars.begin(), d_vars.end(), v) != d_vars.end())
    {
      Node nv = getElimShadowVar(d_closure, n, i);
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
                                               size_t i)
{
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node ii = nm->mkConstInt(Rational(i));
  Node cacheVal = BoundVarManager::getCacheValue(q, n, ii);
  return bvm->mkBoundVar<QElimShadowAttribute>(cacheVal, n[0][i].getType());
}

Node ElimShadowNodeConverter::eliminateShadow(const Node& q)
{
  Assert(q.isClosure());
  NodeManager* nm = NodeManager::currentNM();
  ElimShadowNodeConverter esnc(nm, q);
  // eliminate shadowing in all children
  std::vector<Node> children;
  // drop duplicate variables
  std::vector<Node> vars;
  bool childChanged = false;
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    const Node& v = q[0][i];
    if (std::find(vars.begin(), vars.end(), v) == vars.end())
    {
      vars.push_back(v);
    }
    else
    {
      Node vn = getElimShadowVar(q, q, i);
      vars.push_back(vn);
      childChanged = true;
    }
  }
  if (childChanged)
  {
    children.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, vars));
  }
  else
  {
    children.push_back(q[0]);
  }
  for (size_t i = 1, nchild = q.getNumChildren(); i < nchild; i++)
  {
    children.push_back(esnc.convert(q[i]));
  }
  return NodeManager::currentNM()->mkNode(q.getKind(), children);
}

}  // namespace cvc5::internal
