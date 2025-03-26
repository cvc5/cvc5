/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bound variable manager.
 */

#include "expr/bound_var_manager.h"

#include "expr/node_manager_attributes.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

BoundVarManager::BoundVarManager() {}

BoundVarManager::~BoundVarManager() {}

void BoundVarManager::setNameAttr(Node v, const std::string& name)
{
  v.setAttribute(expr::VarNameAttr(), name);
}

Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2)
{
  return NodeManager::mkNode(Kind::SEXPR, cv1, cv2);
}
Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2, TNode cv3)
{
  return NodeManager::mkNode(Kind::SEXPR, cv1, cv2, cv3);
}

Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2, size_t i)
{
  return NodeManager::mkNode(Kind::SEXPR, cv1, cv2, getCacheValue(i));
}

Node BoundVarManager::getCacheValue(size_t i)
{
  return NodeManager::currentNM()->mkConstInt(Rational(i));
}

Node BoundVarManager::getCacheValue(TNode cv, size_t i)
{
  return getCacheValue(cv, getCacheValue(i));
}

Node BoundVarManager::mkBoundVar(BoundVarId id, Node n, TypeNode tn)
{
  std::tuple<BoundVarId, TypeNode, Node> key(id, tn, n);
  std::map<std::tuple<BoundVarId, TypeNode, Node>, Node>::iterator it =
      d_cache.find(key);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node v = NodeManager::mkBoundVar(tn);
  d_cache[key] = v;
  return v;
}

Node BoundVarManager::mkBoundVar(BoundVarId id,
                                 Node n,
                                 const std::string& name,
                                 TypeNode tn)
{
  Node v = mkBoundVar(id, n, tn);
  setNameAttr(v, name);
  return v;
}

}  // namespace cvc5::internal
