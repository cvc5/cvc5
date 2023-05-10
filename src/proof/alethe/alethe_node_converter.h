/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe node conversion
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE__ALETHE_NODE_CONVERTER_H
#define CVC5__PROOF__ALETHE__ALETHE_NODE_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * This is a helper class for the Alethe post-processor that converts nodes into
 * the form that Alethe expects.
 */
class AletheNodeConverter : public NodeConverter
{
 public:
  AletheNodeConverter() {}
  ~AletheNodeConverter() {}
  /** convert at post-order traversal */
  Node postConvert(Node n) override;

 private:
  /**
   * Make or get an internal symbol with custom name and type.
   */
  Node mkInternalSymbol(const std::string& name, TypeNode tn);
  /**
   * As above but uses the s-expression type.
   */
  Node mkInternalSymbol(const std::string& name);

  /** Maps from internally generated symbols to the built nodes. */
  std::map<std::pair<TypeNode, std::string>, Node> d_symbolsMap;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
