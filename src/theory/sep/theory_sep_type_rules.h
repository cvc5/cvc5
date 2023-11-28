/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of sep.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SEP__THEORY_SEP_TYPE_RULES_H
#define CVC5__THEORY__SEP__THEORY_SEP_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {
namespace sep {

/**
 * Separation empty heap constraint is a nullary predicate. Its type rule
 * returns the Boolean type.
 */
class SepEmpTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Separation points-to is a predicate over any two types that specify the
 * heap, which is not checked by the type system. Its type rule
 * returns the Boolean type.
 */
struct SepPtoTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Separation star is an n-ary Boolean connective. Its type rule ensures all
 * arguments are Boolean. Returns the Boolean type.
 */
struct SepStarTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Separation star is a binary Boolean connective. Its type rule ensures all
 * arguments are Boolean and returns the Boolean type.
 */
struct SepWandTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Separation label annotates formulas with sets that specify the heap. It
 * ensures its first argument is a Boolean, its second argument is a set and
 * returns the Boolean type.
 */
struct SepLabelTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Separation nil is a nullary constructor. Its type is specified via an
 * attribute upon construction and is return in this rule.
 */
struct SepNilTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SEP__THEORY_SEP_TYPE_RULES_H */
