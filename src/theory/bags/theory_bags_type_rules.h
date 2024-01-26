/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

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
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* struct BinaryOperatorTypeRule */

/**
 * Type rule for binary operator bag.subbag to check if the two arguments are
 * bags of the same sort.
 */
struct SubBagTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct SubBagTypeRule */

/**
 * Type rule for binary operator bag.count to check the sort of the first
 * argument matches the element sort of the given bag.
 */
struct CountTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct CountTypeRule */

/**
 * Type rule for binary operator bag.member to check the sort of the first
 * argument matches the element sort of the given bag.
 */
struct MemberTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for bag.duplicate_removal to check the argument is of a bag.
 */
struct DuplicateRemovalTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct DuplicateRemovalTypeRule */

/**
 * Type rule for (bag op e) operator to check the sort of e matches the sort
 * stored in op.
 */
struct BagMakeTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nm,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* struct BagMakeTypeRule */

/**
 * Type rule for (bag.is_singleton B) to check the argument B is a bag.
 */
struct IsSingletonTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct IsSingletonTypeRule */

/**
 * Type rule for (as bag.empty (Bag T)) where T is a type
 */
struct EmptyBagTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct EmptyBagTypeRule */

/**
 * Type rule for (bag.card B) to check the argument B is a bag.
 */
struct CardTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct CardTypeRule */

/**
 * Type rule for (bag.choose B) to check the argument B is a bag.
 */
struct ChooseTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct ChooseTypeRule */

/**
 * Type rule for (bag.from_set ..) to check the argument is of a set.
 */
struct FromSetTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct FromSetTypeRule */

/**
 * Type rule for (bag.to_set ..) to check the argument is of a bag.
 */
struct ToSetTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct ToSetTypeRule */

/**
 * Type rule for (bag.map f B) to make sure f is a unary function of type
 * (-> T1 T2) where B is a bag of type (Bag T1)
 */
struct BagMapTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct BagMapTypeRule */

/**
 * Type rule for (bag.filter p B) to make sure p is a unary predicate of type
 * (-> T Bool) where B is a bag of type (Bag T)
 */
struct BagFilterTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct BagFilterTypeRule */

/**
 * Type rule for (bag.fold f t A) to make sure f is a binary operation of type
 * (-> T1 T2 T2), t of type T2, and A is a bag of type (Bag T1)
 */
struct BagFoldTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct BagFoldTypeRule */

/**
 * Type rule for (bag.partition r A) to make sure r is a binary operation of
 * type
 * (-> T1 T1 Bool), and A is a bag of type (Bag T1)
 */
struct BagPartitionTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct BagFoldTypeRule */

/**
 * Type rule for (table.product A B) to make sure A,B are bags of tuples,
 * and get the type of the cross product
 */
struct TableProductTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct BagFoldTypeRule */

/**
 * Table project is indexed by a list of indices (n_1, ..., n_m). It ensures
 * that the argument is a bag of tuples whose arity k is greater than each n_i
 * for i = 1, ..., m. If the argument is of type (Table T_1 ... T_k), then
 * the returned type is (Table T_{n_1} ... T_{n_m}).
 */
struct TableProjectTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct TableProjectTypeRule */

/**
 * Table aggregate operator is indexed by a list of indices (n_1, ..., n_k).
 * It ensures that it has 3 arguments:
 * - A combining function of type (-> (Tuple T_1 ... T_j) T T)
 * - Initial value of type T
 * - A table of type (Table T_1 ... T_j) where 0 <= n_1, ..., n_k < j
 * the returned type is (Bag T).
 */
struct TableAggregateTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct TableAggregateTypeRule */

/**
 * Table join operator is indexed by a list of indices (m_1, m_k, n_1, ...,
 * n_k). It ensures that it has 2 arguments:
 * - A table of type (Table X_1 ... X_i)
 * - A table of type (Table Y_1 ... Y_j)
 * such that indices has constraints 0 <= m_1, ..., mk, n_1, ..., n_k <=
 * min(i,j) and types has constraints X_{m_1} = Y_{n_1}, ..., X_{m_k} = Y_{n_k}.
 * The returned type is (Table X_1 ... X_i Y_1 ... Y_j)
 */
struct TableJoinTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct TableJoinTypeRule */

/**
 * Table group operator is indexed by a list of indices (n_1, ..., n_k). It
 * ensures that the argument is a table whose arity is greater than each n_i for
 * i = 1, ..., k. If the passed table is of type T, then the returned type is
 * (Bag T), i.e., bag of tables.
 */
struct TableGroupTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct TableGroupTypeRule */

struct BagsProperties
{
  static Cardinality computeCardinality(TypeNode type);

  static bool isWellFounded(TypeNode type);

  static Node mkGroundTerm(TypeNode type);
}; /* struct BagsProperties */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H */
