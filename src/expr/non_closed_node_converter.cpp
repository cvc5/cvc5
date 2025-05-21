/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of non-closed node conversion
 */

#include "expr/non_closed_node_converter.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/arrays_options.h"
#include "smt/env.h"

namespace cvc5::internal {

NonClosedNodeConverter::NonClosedNodeConverter(Env& env)
    : EnvObj(env), NodeConverter(nodeManager())
{
  getNonClosedKinds(env, d_nonClosedKinds);
}

NonClosedNodeConverter::~NonClosedNodeConverter() {}

Node NonClosedNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (d_nonClosedKinds.find(k) != d_nonClosedKinds.end())
  {
    Node sk = SkolemManager::mkPurifySkolem(n);
    d_purifySkolems.push_back(sk);
    return sk;
  }
  return n;
}

bool NonClosedNodeConverter::isClosed(const Env& env, const Node& n)
{
  std::unordered_set<Kind, kind::KindHashFunction> ncks;
  getNonClosedKinds(env, ncks);
  return !expr::hasSubtermKinds(ncks, n);
}

void NonClosedNodeConverter::getNonClosedKinds(
    const Env& env, std::unordered_set<Kind, kind::KindHashFunction>& ncks)
{
  // some kinds may appear in model values that cannot be asserted
  if (!env.getOptions().arrays.arraysExp)
  {
    ncks.insert(Kind::STORE_ALL);
  }
  ncks.insert(Kind::CODATATYPE_BOUND_VARIABLE);
  ncks.insert(Kind::UNINTERPRETED_SORT_VALUE);
  // may appear in certain models e.g. strings of excessive length
  ncks.insert(Kind::WITNESS);
  ncks.insert(Kind::REAL_ALGEBRAIC_NUMBER);
}

const std::vector<Node>& NonClosedNodeConverter::getSkolems() const
{
  return d_purifySkolems;
}

}  // namespace cvc5::internal
