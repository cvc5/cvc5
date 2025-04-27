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
 * The PbNodeManager is responsible for managing the mapping between PbLiteral
 * objects and their corresponding Node representations.
 *
 * Each PbLiteral  is associated with a Boolean Node. This ensures that literals
 * used in pseudo-Boolean constraints have consistent and reusable Node
 * representations.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_NODE_MANAGER_H
#define CVC5__THEORY__BV__PB__PB_NODE_MANAGER_H

#include "expr/node.h"
#include "theory/bv/pb/pb_types.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

typedef std::unordered_map<PbLiteral, Node, PbLiteralHash> PbLiteralToNodeMap;

class PbNodeManager
{
 public:
  PbNodeManager(NodeManager* nm);
  Node literalToNode(const PbLiteral& lit);
  int countLiterals() const;
 private:
  NodeManager* d_nm;
  PbLiteralToNodeMap d_map;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_NODE_MANAGER_H
