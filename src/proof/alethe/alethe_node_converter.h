/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe node conversion
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALETHE__ALETHE_NODE_CONVERTER_H
#define CVC4__PROOF__ALETHE__ALETHE_NODE_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * This is a helper class for the Alethe post-processor that converts nodes into
 * the form that Alethe expects.
 */
class AletheNodeConverter
{
 public:
  AletheNodeConverter();
  ~AletheNodeConverter() {}
  /** convert to internal */
  Node convert(Node n);


 private:
  /** Should only traverse nodes containing closures. */
  bool shouldTraverse(Node n);

  /** Node cache for convert */
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
