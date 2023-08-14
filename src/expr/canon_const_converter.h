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
 * Implementation of subtype elimination node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__EXPR__CANON_CONST_CONVERTER_H
#define CVC4__EXPR__CANON_CONST_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5::internal {

/**
 */
class CanonConstConverter : public NodeConverter
{
 public:
  CanonConstConverter();
  ~CanonConstConverter() {}
  /** convert node n as described above during post-order traversal */
  Node preConvert(Node n) override;
};

}  // namespace cvc5::internal

#endif
