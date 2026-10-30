/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type for rewrites for bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__REWRITES_H
#define CVC5__THEORY__BAGS__REWRITES_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {
namespace bags {

/**
 * Types of rewrites used by bags, each documented by an example in the
 * notation at the top of bags_rewriter.cpp:
 *   previous node
 *   ---> next node
 * The function of BagsRewriter named with a rule documents it further.
 */
enum class Rewrite : uint32_t
{
  /** no rewrite happened */
  NONE,
  /**
   * AGGREGATE_CONST: an aggregate of constants is evaluated
   */
  AGGREGATE_CONST,
  /**
   * BAG_MAKE_COUNT_NEGATIVE: for a constant c <= 0,
   *   (bag x c) ---> (as bag.empty (Bag T))
   */
  BAG_MAKE_COUNT_NEGATIVE,
  CARD_DISJOINT,
  /**
   * CARD_BAG_MAKE: for a constant c > 0,
   *   (bag.card (bag x c)) ---> c
   */
  CARD_BAG_MAKE,
  /**
   * CHOOSE_BAG_MAKE: for a constant c > 0,
   *   (bag.choose (bag x c)) ---> x
   */
  CHOOSE_BAG_MAKE,
  /**
   * CONSTANT_EVALUATION: a term of constants is evaluated:
   *   (bag.union_disjoint (bag 1 2) (bag 1 3)) ---> (bag 1 5)
   */
  CONSTANT_EVALUATION,
  /**
   * COUNT_EMPTY:
   *   (bag.count x (as bag.empty (Bag T))) ---> 0
   */
  COUNT_EMPTY,
  /**
   * COUNT_BAG_MAKE: for a constant c > 0,
   *   (bag.count x (bag x c)) ---> c
   */
  COUNT_BAG_MAKE,
  /**
   * SETOF_BAG_MAKE:
   *   (bag.setof (bag x c)) ---> (bag x 1)
   * for a constant c > 0, and otherwise
   *   (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
   */
  SETOF_BAG_MAKE,
  /**
   * EQ_CONST_FALSE: for distinct constants A and B,
   *   (= A B) ---> false
   */
  EQ_CONST_FALSE,
  /**
   * EQ_REFL:
   *   (= A A) ---> true
   */
  EQ_REFL,
  /**
   * EQ_SYM: for A < B,
   *   (= B A) ---> (= A B)
   */
  EQ_SYM,
  /**
   * FILTER_CONST: a filter of a constant is evaluated:
   *   (bag.filter p (bag "a" 3))
   *   ---> (ite (p "a") (bag "a" 3) (as bag.empty (Bag String)))
   */
  FILTER_CONST,
  /**
   * FILTER_BAG_MAKE:
   *   (bag.filter p (bag x c)) ---> (bag x (ite (p x) c 0))
   */
  FILTER_BAG_MAKE,
  /**
   * FILTER_UNION_DISJOINT:
   *   (bag.filter p (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   */
  FILTER_UNION_DISJOINT,
  /**
   * FILTER_MAP:
   *   (bag.filter (lambda ((s U)) p) (bag.map (lambda ((t T)) e) A))
   *   ---> (bag.map (lambda ((t T)) e)
   *                 (bag.filter (lambda ((t T)) p[s := e]) A))
   */
  FILTER_MAP,
  /**
   * MAP_MAP:
   *   (bag.map (lambda ((s U)) e) (bag.map (lambda ((t T)) g) A))
   *   ---> (bag.map (lambda ((t T)) e[s := g]) A)
   */
  MAP_MAP,
  /**
   * AGGREGATE_MAP, grouping the rows of a map by the columns it copies:
   *   ((_ table.aggr 0) (lambda ((s U) (acc S)) b) i
   *                     (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
   *                                                     ((_ tuple.select 0)
   *                                                      t)))
   *                              X))
   *   ---> ((_ table.aggr 2) (lambda ((t T) (acc S))
   *                            b[s := (tuple ((_ tuple.select 2) t)
   *                                          ((_ tuple.select 0) t))])
   *                          i X)
   */
  AGGREGATE_MAP,
  /**
   * FILTER_TRUE:
   *   (bag.filter (lambda ((t T)) true) A) ---> A
   */
  FILTER_TRUE,
  /**
   * FILTER_FALSE, a filter no row passes:
   *   (bag.filter (lambda ((t T)) false) A) ---> (as bag.empty (Bag T))
   *   (bag.filter (lambda ((t T)) (and p (not p))) A)
   *   ---> (as bag.empty (Bag T))
   */
  FILTER_FALSE,
  /**
   * CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N the
   * id of f's alpha key, when that is safe:
   *   (lambda ((s T)) (> ((_ tuple.select 0) s) 3))
   *   ---> (lambda ((t_N T)) (> ((_ tuple.select 0) t_N) 3))
   * f's body is first simplified, see simplifyIteSame.
   */
  CANONICAL_VARIABLE,
  /**
   * AGGREGATE_SORT_OUTPUT, the columns of the aggregate's rows in one order,
   * copies of group columns first:
   *   ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a1 ((_ tuple.select 0)
   *                                                      t)))
   *                     (tuple i1 i0) X)
   *   ---> (bag.map (lambda ((r S')) (tuple ((_ tuple.select 1) r)
   *                                         ((_ tuple.select 0) r)))
   *                 ((_ table.aggr 0) (lambda ((t T) (acc S'))
   *                                     (tuple ((_ tuple.select 0) t) a1'))
   *                                   (tuple i0 i1) X))
   */
  AGGREGATE_SORT_OUTPUT,
  /**
   * AGGREGATE_NO_KEYS, one group of all of X, even an empty X:
   *     ((_ table.aggr) f i X) ---> (bag (bag.fold f i X) 1)
   */
  AGGREGATE_NO_KEYS,
  /**
   * FOLD_TUPLE, a fold of tuples whose components read their own
   * accumulator only:
   *   (bag.fold (lambda ((t T) (acc (Tuple Int Int))) (tuple b0 b1))
   *             (tuple i0 i1) X)
   *   ---> (tuple (bag.fold (lambda ((t T) (a Int)) b0') i0 X)
   *               (bag.fold (lambda ((t T) (a Int)) b1') i1 X))
   */
  FOLD_TUPLE,
  /**
   * AGGREGATE_DEAD_COLUMNS, a column of the aggregate nothing reads:
   *   (bag.map h ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 a1 a2))
   *                                (tuple i0 i1 i2) X))
   *   ---> (bag.map h' ((_ table.aggr 0) (lambda ((t T) (acc S'))
   *                                        (tuple a0 a2'))
   *                                      (tuple i0 i2) X))
   * also under a filter between the map and the aggregate
   */
  AGGREGATE_DEAD_COLUMNS,
  /**
   * FOLD_CONSTANT_STEP:
   *   (bag.fold (lambda ((t T) (acc S)) c) i X)
   *   ---> (ite (= X (as bag.empty (Bag T))) i c)
   * for c reading neither t nor acc
   */
  FOLD_CONSTANT_STEP,
  /**
   * MAP_FIXED_COLUMNS, the constants the filter fixes columns to:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)))
   *            (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5))
   *                        X))
   *   ---> (bag.map (lambda ((t T)) (tuple 5))
   *                 (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s)
   *                                                5))
   *                             X))
   * and, over an aggregate whose counter the filter tests, the constants
   * its groups compute (see reachedGroupConstants)
   */
  MAP_FIXED_COLUMNS,
  /**
   * SETOF_PROJECTION_SORT, the set of a projection onto columns in another
   * order than theirs as the set of the projection onto the sorted columns,
   * mapped back by the permutation (see rewriteSetofOfMap):
   *   (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
   *                                              ((_ tuple.select 0) t)))
   *                       Y))
   *   ---> (bag.map (lambda ((r U)) (tuple ((_ tuple.select 1) r)
   *                                        ((_ tuple.select 0) r)))
   *                 (bag.setof (bag.map (lambda ((t T))
   *                                       (tuple ((_ tuple.select 0) t)
   *                                              ((_ tuple.select 2) t)))
   *                                     Y)))
   */
  SETOF_PROJECTION_SORT,
  /**
   * AGGREGATE_KEYED, see keyedAggregateRows: under a filter that drops the
   * row of initial values (see rejectsInitialRow),
   *   (bag.filter Q ((_ table.aggr 0) (lambda ((t T) (acc S)) b) i X))
   *   ---> (bag.filter Q (bag.map (lambda ((t T)) b[acc := i]) X))
   * for 0 a key of X, and for an aggregate component of a product whose
   * groups the filter keeps reached ones of (see reachedComponents)
   */
  AGGREGATE_KEYED,
  /**
   * NOT_NULL_COLUMNS, the null tests of columns that are never null decided,
   * in filters, maps, folds and aggregates (see assumeNonNull,
   * nonNullColumns); with column 1 of X never null,
   *   (bag.filter (lambda ((t T))
   *                 (and (nullable.is_some ((_ tuple.select 1) t)) p))
   *               X)
   *   ---> (bag.filter (lambda ((t T)) (and true p)) X)
   */
  NOT_NULL_COLUMNS,
  /**
   * FILTER_NULLABLE_TRUTH, the two conjuncts that say a nullable Boolean X
   * holds as the one formula they say (see normalizeTruth):
   *   (bag.filter (lambda ((t T)) (and (nullable.is_some X) (nullable.val X)))
   *               A)
   *   ---> (bag.filter (lambda ((t T)) (ite c b false)) A)
   * for X = (ite c (nullable.some b) (as nullable.null (Nullable Bool)))
   */
  FILTER_NULLABLE_TRUTH,
  /**
   * MAP_EQUAL_COLUMNS, the first of the columns the filter equates:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)))
   *            (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                           ((_ tuple.select 2) s)))
   *                        X))
   *   ---> (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
   *                 (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                                ((_ tuple.select 2) s)))
   *                             X))
   */
  MAP_EQUAL_COLUMNS,
  /**
   * MAP_IDENTITY:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
   *                                   ((_ tuple.select 1) t)))
   *            X)
   *   ---> X
   */
  MAP_IDENTITY,
  /**
   * FILTER_CONFLICTING_CONSTANTS:
   *   (bag.filter (lambda ((t T)) (and (= ((_ tuple.select 0) t) 1)
   *                                    (= ((_ tuple.select 0) t) 2)))
   *               X)
   *   ---> (as bag.empty (Bag T))
   * and the conjuncts the others imply go: (nullable.is_some a) beside
   * (= a (nullable.some 5)), the null test of a value that a membership
   * puts in a never-null column, (>= (* a b) 1) beside (>= a 1) and
   * (>= b 1)
   */
  FILTER_CONFLICTING_CONSTANTS,
  /**
   * PROJECT_TO_MAP: a projection is a map, which the map rules then reach:
   *   ((_ table.project 1 0) X)
   *   ---> (bag.map (lambda ((t T)) ((_ tuple.project 1 0) t)) X)
   */
  PROJECT_TO_MAP,
  /**
   * ALL_EMPTY:
   *   (bag.all p (as bag.empty (Bag T))) ---> true
   */
  ALL_EMPTY,
  /**
   * ALL_BAG_MAKE:
   *   (bag.all p (bag x c)) ---> (or (p x) (<= c 0))
   */
  ALL_BAG_MAKE,
  /**
   * ALL_UNION_DISJOINT:
   *   (bag.all p (bag.union_disjoint A B))
   *   ---> (and (bag.all p A) (bag.all p B))
   */
  ALL_UNION_DISJOINT,
  /**
   * ALL_FILTER:
   *   (bag.all p A) ---> (= (bag.filter p A) A)
   */
  ALL_FILTER,
  /**
   * SOME_EMPTY:
   *   (bag.some p (as bag.empty (Bag T))) ---> false
   */
  SOME_EMPTY,
  /**
   * SOME_BAG_MAKE:
   *   (bag.some p (bag x c)) ---> (and (> c 0) (p x))
   */
  SOME_BAG_MAKE,
  /**
   * SOME_UNION_DISJOINT:
   *   (bag.some p (bag.union_disjoint A B))
   *   ---> (or (bag.some p A) (bag.some p B))
   */
  SOME_UNION_DISJOINT,
  /**
   * SOME_FILTER:
   *   (bag.some p A)
   *   ---> (not (= (bag.filter p A) (as bag.empty (Bag T))))
   */
  SOME_FILTER,
  FROM_SINGLETON,
  /**
   * FOLD_BAG: for a constant c > 0,
   *   (bag.fold f t (bag x c)) ---> (f x (f x .. (f x t))), c times
   */
  FOLD_BAG,
  /**
   * FOLD_CONST: a fold over a constant is evaluated
   */
  FOLD_CONST,
  /**
   * FOLD_UNION_DISJOINT: for A < B,
   *   (bag.fold f t (bag.union_disjoint A B))
   *   ---> (bag.fold f (bag.fold f t A) B)
   */
  FOLD_UNION_DISJOINT,
  /**
   * IDENTICAL_NODES: for bags A,
   *   (= A A) ---> true
   */
  IDENTICAL_NODES,
  /**
   * INTERSECTION_EMPTY_LEFT:
   *   (bag.inter_min (as bag.empty (Bag T)) A)
   *   ---> (as bag.empty (Bag T))
   */
  INTERSECTION_EMPTY_LEFT,
  /**
   * INTERSECTION_EMPTY_RIGHT:
   *   (bag.inter_min A (as bag.empty (Bag T)))
   *   ---> (as bag.empty (Bag T))
   */
  INTERSECTION_EMPTY_RIGHT,
  /**
   * INTERSECTION_SAME:
   *   (bag.inter_min A A) ---> A
   */
  INTERSECTION_SAME,
  /**
   * INTERSECTION_SHARED_LEFT:
   *   (bag.inter_min A (bag.union_disjoint A B)) ---> A
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  INTERSECTION_SHARED_LEFT,
  /**
   * INTERSECTION_SHARED_RIGHT:
   *   (bag.inter_min (bag.union_disjoint A B) A) ---> A
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  INTERSECTION_SHARED_RIGHT,
  IS_SINGLETON_BAG_MAKE,
  /**
   * MAP_CONST: a map of a constant is evaluated:
   *   (bag.map f (bag "a" 3)) ---> (bag (f "a") 3)
   */
  MAP_CONST,
  /**
   * MAP_BAG_MAKE:
   *   (bag.map f (bag x c)) ---> (bag (f x) c)
   */
  MAP_BAG_MAKE,
  /**
   * MAP_UNION_DISJOINT:
   *   (bag.map f (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint (bag.map f A) (bag.map f B))
   */
  MAP_UNION_DISJOINT,
  /**
   * MEMBER:
   *   (bag.member x A) ---> (>= (bag.count x A) 1)
   */
  MEMBER,
  /**
   * PARTITION_CONST: a partition of a constant is evaluated
   */
  PARTITION_CONST,
  /**
   * PRODUCT_EMPTY:
   *   (table.product (as bag.empty (Bag T)) B) ---> (as bag.empty (Bag V))
   * and with the empty bag second
   */
  PRODUCT_EMPTY,
  /**
   * REMOVE_FROM_UNION:
   *   (bag.difference_remove A (bag.union_disjoint A B))
   *   ---> (as bag.empty (Bag T))
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  REMOVE_FROM_UNION,
  /**
   * REMOVE_MIN:
   *   (bag.difference_remove (bag.inter_min A B) A)
   *   ---> (as bag.empty (Bag T))
   * and for (bag.inter_min B A)
   */
  REMOVE_MIN,
  /**
   * REMOVE_RETURN_LEFT:
   *   (bag.difference_remove A (as bag.empty (Bag T))) ---> A
   *   (bag.difference_remove (as bag.empty (Bag T)) B)
   *   ---> (as bag.empty (Bag T))
   */
  REMOVE_RETURN_LEFT,
  /**
   * REMOVE_SAME:
   *   (bag.difference_remove A A) ---> (as bag.empty (Bag T))
   */
  REMOVE_SAME,
  /**
   * SUB_BAG:
   *   (bag.subbag A B)
   *   ---> (= (bag.difference_subtract A B) (as bag.empty (Bag T)))
   */
  SUB_BAG,
  /**
   * SUBTRACT_DISJOINT_SHARED_LEFT:
   *   (bag.difference_subtract (bag.union_disjoint A B) A) ---> B
   */
  SUBTRACT_DISJOINT_SHARED_LEFT,
  /**
   * SUBTRACT_DISJOINT_SHARED_RIGHT:
   *   (bag.difference_subtract (bag.union_disjoint B A) A) ---> B
   */
  SUBTRACT_DISJOINT_SHARED_RIGHT,
  /**
   * SUBTRACT_FROM_UNION:
   *   (bag.difference_subtract A (bag.union_disjoint A B))
   *   ---> (as bag.empty (Bag T))
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  SUBTRACT_FROM_UNION,
  /**
   * SUBTRACT_MIN:
   *   (bag.difference_subtract (bag.inter_min A B) A)
   *   ---> (as bag.empty (Bag T))
   * and for (bag.inter_min B A)
   */
  SUBTRACT_MIN,
  /**
   * SUBTRACT_RETURN_LEFT:
   *   (bag.difference_subtract A (as bag.empty (Bag T))) ---> A
   *   (bag.difference_subtract (as bag.empty (Bag T)) B)
   *   ---> (as bag.empty (Bag T))
   */
  SUBTRACT_RETURN_LEFT,
  /**
   * SUBTRACT_SAME:
   *   (bag.difference_subtract A A) ---> (as bag.empty (Bag T))
   */
  SUBTRACT_SAME,
  TO_SINGLETON,
  /**
   * UNION_DISJOINT_EMPTY_LEFT:
   *   (bag.union_disjoint (as bag.empty (Bag T)) A) ---> A
   */
  UNION_DISJOINT_EMPTY_LEFT,
  /**
   * UNION_DISJOINT_EMPTY_RIGHT:
   *   (bag.union_disjoint A (as bag.empty (Bag T))) ---> A
   */
  UNION_DISJOINT_EMPTY_RIGHT,
  /**
   * UNION_DISJOINT_MAX_MIN:
   *   (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B))
   *   ---> (bag.union_disjoint A B)
   */
  UNION_DISJOINT_MAX_MIN,
  /**
   * UNION_MAX_EMPTY:
   *   (bag.union_max (as bag.empty (Bag T)) A) ---> A
   */
  UNION_MAX_EMPTY,
  /**
   * UNION_MAX_SAME_OR_EMPTY:
   *   (bag.union_max A A) ---> A
   *   (bag.union_max A (as bag.empty (Bag T))) ---> A
   */
  UNION_MAX_SAME_OR_EMPTY,
  /**
   * UNION_MAX_UNION_LEFT:
   *   (bag.union_max A (bag.union_max A B)) ---> (bag.union_max A B)
   * also for bag.union_disjoint and for (bag.union_max B A)
   */
  UNION_MAX_UNION_LEFT,
  /**
   * UNION_MAX_UNION_RIGHT:
   *   (bag.union_max (bag.union_max A B) A) ---> (bag.union_max A B)
   * also for bag.union_disjoint and for (bag.union_max B A)
   */
  UNION_MAX_UNION_RIGHT,
};

/**
 * Converts an rewrite to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param r The rewrite
 * @return The name of the rewrite
 */
const char* toString(Rewrite r);

/**
 * Writes an rewrite name to a stream.
 *
 * @param out The stream to write to
 * @param r The rewrite to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Rewrite r);

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__REWRITES_H */
