/*********************                                                        */
/*! \file bound_var_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bound variable manager
 **/

#include "expr/bound_var_manager.h"

#include "expr/node_manager_attributes.h"

namespace CVC4 {

// TODO: only enable when proofs are enabled
BoundVarManager::BoundVarManager() : d_keepCacheVals(true) {}

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

Node BoundVarManager::getCacheValue(TNode cv1, TNode cv2, size_t i)
{
  return NodeManager::currentNM()->mkNode(
      kind::SEXPR, cv1, cv2, getCacheValue(i));
}

Node BoundVarManager::getCacheValue(size_t i)
{
  return NodeManager::currentNM()->mkConst(Rational(i));
}

Node BoundVarManager::getCacheValue(TNode cv, size_t i)
{
  return getCacheValue(cv, getCacheValue(i));
}

}  // namespace CVC4
