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
 * Bound variable manager.
 */

#include "expr/bound_var_manager.h"

#include "expr/node_manager_attributes.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

BoundVarManager::BoundVarManager() : d_keepCacheVals(false) {}

BoundVarManager::~BoundVarManager() {}

void BoundVarManager::enableKeepCacheValues(bool isEnabled)
{
  d_keepCacheVals = isEnabled;
}

void BoundVarManager::setNameAttr(Node v, const std::string& name)
{
  v.setAttribute(expr::VarNameAttr(), name);
}

Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2)
{
  return NodeManager::currentNM()->mkNode(kind::SEXPR, cv1, cv2);
}
Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2, TNode cv3)
{
  return NodeManager::currentNM()->mkNode(kind::SEXPR, cv1, cv2, cv3);
}

Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2, size_t i)
{
  return NodeManager::currentNM()->mkNode(
      kind::SEXPR, cv1, cv2, getCacheValue(i));
}

Node BoundVarManager::getCacheValue(size_t i)
{
  return NodeManager::currentNM()->mkConstInt(Rational(i));
}

Node BoundVarManager::getCacheValue(TNode cv, size_t i)
{
  return getCacheValue(cv, getCacheValue(i));
}

}  // namespace cvc5::internal
