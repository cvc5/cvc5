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
 * Implementation of annotation elimination node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__EXPR__ANNOTATION_ELIM_NODE_CONVERTER_H
#define CVC4__EXPR__ANNOTATION_ELIM_NODE_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {

/**
 * This converts a node into one that does not involve annotations for
 * quantified formulas. In other words, the third child is dropped for all
 * closure terms with 3 children.
 */
class AnnotationElimNodeConverter : public NodeConverter
{
 public:
  AnnotationElimNodeConverter();
  ~AnnotationElimNodeConverter() {}
  /** convert node n as described above during post-order traversal */
  Node postConvert(Node n) override;
};

}  // namespace cvc5::internal

#endif
