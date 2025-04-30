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

#include "expr/skolem_manager.h"

namespace cvc5::internal {

NonClosedNodeConverter::NonClosedNodeConverter(Env& env) : EnvObj(env), NodeConverter(nodeManager()) {
  // some kinds may appear in model values that cannot be asserted
  d_nonClosedKinds.insert(Kind::STORE_ALL);
  d_nonClosedKinds.insert(Kind::CODATATYPE_BOUND_VARIABLE);
  d_nonClosedKinds.insert(Kind::UNINTERPRETED_SORT_VALUE);
  // may appear in certain models e.g. strings of excessive length
  d_nonClosedKinds.insert(Kind::WITNESS);
  d_nonClosedKinds.insert(Kind::REAL_ALGEBRAIC_NUMBER);
  
}
NonClosedNodeConverter::~NonClosedNodeConverter() {}
Node NonClosedNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (d_nonClosedKinds.find(k)!=d_nonClosedKinds.end())
  {
    Node sk = SkolemManager::mkPurifySkolem(n);
    d_purifySkolems.push_back(sk);
    return sk;
  }
  return n;
}
const std::vector<Node>& NonClosedNodeConverter::getSkolems() const { return d_purifySkolems; }

}  // namespace cvc5::internal

