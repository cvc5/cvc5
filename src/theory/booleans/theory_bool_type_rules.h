/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of boolean.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY_BOOL_TYPE_RULES_H
#define CVC5__THEORY_BOOL_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace boolean {

class BooleanTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class IteTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace boolean
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY_BOOL_TYPE_RULES_H */
