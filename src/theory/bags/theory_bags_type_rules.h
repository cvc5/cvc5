/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory type rules.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H
#define CVC5__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H

#include "expr/node.h"

namespace cvc5 {

class NodeManager;
class TypeNode;

namespace theory {
namespace bags {

/**
 * Type rule for binary operators (bag.union_max, bag.union_disjoint,
 * bag.inter_min bag.difference_subtract, bag.difference_remove) to check
 * if the two arguments are bags of the same sort.
 */
struct BinaryOperatorTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* struct BinaryOperatorTypeRule */

/**
 * Type rule for binary operator bag.subbag to check if the two arguments are
 * bags of the same sort.
 */
struct SubBagTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct SubBagTypeRule */

/**
 * Type rule for binary operator bag.count to check the sort of the first
 * argument matches the element sort of the given bag.
 */
struct CountTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct CountTypeRule */

/**
 * Type rule for binary operator bag.member to check the sort of the first
 * argument matches the element sort of the given bag.
 */
struct MemberTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for bag.duplicate_removal to check the argument is of a bag.
 */
struct DuplicateRemovalTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct DuplicateRemovalTypeRule */

/**
 * Type rule for (bag op e) operator to check the sort of e matches the sort
 * stored in op.
 */
struct BagMakeTypeRule
{
  static TypeNode computeType(NodeManager* nm, TNode n, bool check);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* struct BagMakeTypeRule */

/**
 * Type rule for (bag.is_singleton B) to check the argument B is a bag.
 */
struct IsSingletonTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct IsSingletonTypeRule */

/**
 * Type rule for (as bag.empty (Bag T)) where T is a type
 */
struct EmptyBagTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct EmptyBagTypeRule */

/**
 * Type rule for (bag.card B) to check the argument B is a bag.
 */
struct CardTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct CardTypeRule */

/**
 * Type rule for (bag.choose B) to check the argument B is a bag.
 */
struct ChooseTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct ChooseTypeRule */

/**
 * Type rule for (bag.from_set ..) to check the argument is of a set.
 */
struct FromSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct FromSetTypeRule */

/**
 * Type rule for (bag.to_set ..) to check the argument is of a bag.
 */
struct ToSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct ToSetTypeRule */

/**
 * Type rule for (bag.map f B) to make sure f is a unary function of type
 * (-> T1 T2) where B is a bag of type (Bag T1)
 */
struct BagMapTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct BagMapTypeRule */

/**
 * Type rule for (bag.filter p B) to make sure p is a unary predicate of type
 * (-> T Bool) where B is a bag of type (Bag T)
 */
struct BagFilterTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct BagFilterTypeRule */

/**
 * Type rule for (bag.fold f t A) to make sure f is a binary operation of type
 * (-> T1 T2 T2), t of type T2, and B is a bag of type (Bag T1)
 */
struct BagFoldTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct BagFoldTypeRule */

/**
 * Type rule for (table.product A B) to make sure A,B are bags of tuples,
 * and get the type of the cross product
 */
struct TableProductTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct BagFoldTypeRule */

struct BagsProperties
{
  static Cardinality computeCardinality(TypeNode type);

  static bool isWellFounded(TypeNode type);

  static Node mkGroundTerm(TypeNode type);
}; /* struct BagsProperties */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H */
