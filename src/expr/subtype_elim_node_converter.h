/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of subtype elimination node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__EXPR__SUBTYPE_ELIM_NODE_CONVERTER_H
#define CVC4__PROOF__EXPR__SUBTYPE_ELIM_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5 {

/**
 * This converts a node into one that does not involve (arithmetic) subtyping.
 * In particular, all applications of arithmetic symbols that involve at least
 * one (strict) Real child are such that all children are cast to real.
 */
class SubtypeElimNodeConverter : public NodeConverter
{
 public:
  SubtypeElimNodeConverter();
  ~SubtypeElimNodeConverter() {}
  /** convert node n as described above during post-order traversal */
  Node postConvert(Node n) override;
 private:
  /** Is real type (not integer)? */
  static bool isRealTypeStrict(TypeNode tn);
};

}  // namespace cvc5

#endif
