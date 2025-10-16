/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of beta reduction node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__EXPR__BETA_REDUCE_NODE_CONVERTER_H
#define CVC4__PROOF__EXPR__BETA_REDUCE_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5::internal {

/**
 * Applies beta-reduction to all subterms
 */
class BetaReduceNodeConverter : public NodeConverter
{
 public:
  BetaReduceNodeConverter(NodeManager * nm) : NodeConverter(nm) {}
  ~BetaReduceNodeConverter() {}
  /** convert node n as described above during post-order traversal */
  Node postConvert(Node n) override;
};

}  // namespace cvc5::internal

#endif