/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory type rules.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__THEORY_SETS_TYPE_RULES_H
#define CVC5__THEORY__SETS__THEORY_SETS_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace sets {

/**
 * Type rule for binary operators (set.union, set.inter_min, set.minus) to check
 * if the two arguments are sets of the same sort.
 */
struct SetsBinaryOperatorTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
};

/**
 * Type rule for binary operator set.subset to check if the two arguments are
 * sets of the same sort.
 */
struct SubsetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for binary operator set.member to check the sort of the first
 * argument matches the element sort of the given set.
 */
struct MemberTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.singleton (SetSingletonOp t) x) to check the sort of x
 * matches the sort t.
 */
struct SingletonTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);

  static bool computeIsConst(NodeManager* nodeManager, TNode n);
};

/**
 * Type rule for (as set.empty (Set T)) where T is a type
 */
struct EmptySetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (bag.card A) to check the argument A is a set.
 */
struct CardTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.complement A) to check the argument A is a set.
 */
struct ComplementTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (as set.universe (Set T)) where T is a type
 */
struct UniverseSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.comprehension ((x1 T1) ... (xn Tn)) predicate body)
 * that checks x1 ... xn are bound variables, predicate is a boolean term,
 * and computes the type (Set T) where T is the type of body
 */
struct ComprehensionTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.choose A) to check the argument A is a set.
 */
struct ChooseTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.is_singleton A) to check the argument A is a set.
 */
struct IsSingletonTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.insert e1 ... en A) that checks the sorts of e1, ..., en
 * match the element sort of the set A
 */
struct InsertTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for (set.map f S) to make sure f is a unary function of type
 * (-> T1 T2) where S is a bag of type (Set T1)
 */
struct SetMapTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct SetMapTypeRule */

/**
 * Type rule for binary operators (rel.join, rel.product) to check
 * if the two arguments are relations (set of tuples).
 * For arguments A of type (Set (Tuple A1 ... Am)) and B of type
 * (Set (Tuple B1 ... Bn)):
 * - (rel.product A B): it computes the type (Set (Tuple (A1 ... Am B1 ... Bn)).
 * - (rel.join A B) it checks that m, n > 1 and Am = B1 and computes the type
 *   (Set (Tuple (A1 ... Am-1 B2 ... Bn)).
 */
struct RelBinaryOperatorTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for unary operator (rel.transpose A) to check that A is a relation
 * (set of Tuples). For an argument A of type (Set (Tuple A1 ... An))
 * it reveres A1 ... An and computes the type (Set (Tuple An ... A1)).
 */
struct RelTransposeTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for unary operator (rel.tclosure A) to check that A is a binary
 * relation of type (Set (Tuple T T)), where T is a type
 */
struct RelTransClosureTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for operator (rel.join_image A c) that checks A is a binary
 * relation of type (Set (Tuple T T)), where T is a type, and c is an integer
 * term (in fact c should be a non-negative constant, otherwise a logic
 * exception is thrown TheorySetsPrivate::preRegisterTerm).
 */
struct JoinImageTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for unary operator (rel.iden A) to check that A is a unary relation
 * of type (Set (Tuple T)) and computes the type (Set (Tuple T T)) for the
 * identity
 */
struct RelIdenTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct SetsProperties
{
  static Cardinality computeCardinality(TypeNode type);

  static bool isWellFounded(TypeNode type);

  static Node mkGroundTerm(TypeNode type);
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SETS__THEORY_SETS_TYPE_RULES_H */
