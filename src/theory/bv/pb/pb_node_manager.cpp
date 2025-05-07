/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PbNodemanager impls
 */

#include "theory/bv/pb/pb_node_manager.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

PbNodeManager::PbNodeManager(NodeManager* nm) : d_nm(nm) {}

Node PbNodeManager::literalToNode(const PbLiteral& lit)
{
  return d_map
      .try_emplace(lit,
                   d_nm->mkBoundVar((std::ostringstream() << lit).str(),
                                    d_nm->booleanType()))
      .first->second;
}

int PbNodeManager::countLiterals() const { return d_map.size(); }

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
