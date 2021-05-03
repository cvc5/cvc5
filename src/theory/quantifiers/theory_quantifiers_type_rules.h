/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H
#define CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

struct QuantifierTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct QuantifierBoundVarListTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct QuantifierInstPatternTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct QuantifierAnnotationTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct QuantifierInstPatternListTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H */
