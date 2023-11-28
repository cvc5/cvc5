/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type rules for the builtin theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H
#define CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

#include <sstream>

namespace cvc5::internal {
namespace theory {
namespace builtin {

class EqualityTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class DistinctTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class SExprTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class UninterpretedSortValueTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class WitnessTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class ApplyIndexedSymbolicTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class SortProperties
{
 public:
  static bool isWellFounded(TypeNode type) { return true; }
  static Node mkGroundTerm(TypeNode type);
};

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H */
