/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite field theory type rules.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__THEORY_FF_TYPE_RULES_H
#define CVC5__THEORY__FF__THEORY_FF_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/* -------------------------------------------------------------------------- */

struct FiniteFieldProperties
{
  static Cardinality computeCardinality(TypeNode type);
};

/* -------------------------------------------------------------------------- */

class FiniteFieldConstantTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/* -------------------------------------------------------------------------- */

class FiniteFieldFixedFieldTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__THEORY_FF_TYPE_RULES_H */
