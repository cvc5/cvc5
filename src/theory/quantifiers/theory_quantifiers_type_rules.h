/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Type rule used for FORALL and EXISTS. Ensures the first argument is a
 * bound variable list, the second argument has Boolean Type, and the third
 * argument (if it exists) is an instantiation pattern list. Returns the
 * Boolean type.
 *
 * Furthermore ensures that certain annotations (e.g., for INST_POOL) are well
 * formed. In particular, instantiation pool annotations specify how to
 * instantiate this quantified formula. These must specify n sets, where n
 * is the number of variables of this quantified formula.
 */
struct QuantifierTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for bound variable lists. Ensures its children are bound variables,
 * and returns the bound variable list type.
 */
struct QuantifierBoundVarListTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for instantiation patterns. This checks for a common mistake
 * of using terms instead of term lists in pattern annotations, and returns
 * the instantiation pattern type.
 */
struct QuantifierInstPatternTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * A quantifier annotation, which returns the instantiation pattern type.
 *
 * Furthermore ensures well-formedness of instantiation attributes with more
 * that one child, which must have a keyword specified as a constant string as
 * the first child (the remaining children can be arbitrary).
 */
struct QuantifierAnnotationTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for instantiation pattern lists. Ensures its children are either
 * instantiation patterns, instantiation attributes, or other allowed
 * annotations. Returns the instantiation pattern list type.
 */
struct QuantifierInstPatternListTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H */
