/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory rewriter.
 */

#include <map>
#include <unordered_map>

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H
#define CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H

#include <set>
#include <utility>
#include <vector>

#include "theory/bags/rewrites.h"
#include "theory/theory_rewriter.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

/** a class represents the result of rewriting bag nodes */
struct BagsRewriteResponse
{
  BagsRewriteResponse();
  BagsRewriteResponse(Node n, Rewrite rewrite);
  /** the rewritten node */
  Node d_node;
  /** type of rewrite used by bags */
  Rewrite d_rewrite;

}; /* struct BagsRewriteResponse */

/**
 * Keys and NOT NULL columns of table constants that the input asserts. The
 * rewriter of the theory has none, so what it returns depends only on the
 * node it rewrites. Static learning reads them off the top-level assertions
 * (BagsRewriter::readTableFact) and, with a BagsRewriter of its own that has
 * them, learns F => (= t t') for the terms t of the input (see
 * TableFactsLearner). For X : (Bag (Tuple Int (Nullable Int) Int)), the
 * assertions
 *
 *   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
 *   (= (bag.filter
 *        (lambda ((t (Tuple Int (Nullable Int) Int)))
 *          (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
 *        X)
 *      (as bag.empty (Bag (Tuple Int (Nullable Int) Int))))
 *
 * give d_keys = {X: {{0, 2}}} and d_notNull = {X: {1}}.
 */
struct TableFacts
{
  /** whether no table has a key or a NOT NULL column */
  bool empty() const { return d_keys.empty() && d_notNull.empty(); }
  /** the keys of each table constant */
  std::map<Node, std::vector<std::set<uint32_t>>> d_keys;
  /** the NOT NULL columns of each table constant */
  std::map<Node, std::set<uint32_t>> d_notNull;
};

/**
 * The rewriter of bags and tables. Its normal form for
 * SELECT h FROM X1, X2 WHERE P is
 *
 *   (bag.map h (bag.filter P (table.product X1 X2)))
 *
 * Each function below lists its rules, each a Rewrite id (see rewrites.h),
 * with an example.
 */
class BagsRewriter : public TheoryRewriter
{
 public:
  /**
   * With higherOrder false, FILTER_MAP, MAP_MAP and PROJECT_TO_MAP do not
   * apply: they build lambdas, which a logic without higher-order terms
   * rejects. With facts null, as for the rewriter of the theory, no table has
   * a key or a NOT NULL column, and the rules that need one do not apply.
   */
  BagsRewriter(NodeManager* nm,
               Rewriter* r,
               HistogramStat<Rewrite>* statistics = nullptr,
               bool higherOrder = false,
               const TableFacts* facts = nullptr);

  /**
   * Calls the function below for n's kind. A node of constants is evaluated:
   *
   * - CONSTANT_EVALUATION
   *     (bag.union_disjoint (bag 1 2) (bag 1 3))
   *     ---> (bag 1 5)
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * Calls preRewriteEqual, rewriteSubBag or rewriteMember.
   */
  RewriteResponse preRewrite(TNode n) override;

  /**
   * Adds to facts the key or the NOT NULL column that the literal lit states
   * of a table constant, and returns whether it states one (see TableFacts,
   * readKey and readNotNull). TableFactsLearner calls it on each top-level
   * assertion, which the rewriter of the theory has already rewritten.
   */
  bool readTableFact(TNode lit, TableFacts& facts) const;

 private:
  // ---------------------------------------------------------------------------
  // The rules of each kind. A function returns its argument with
  // Rewrite::NONE when no rule applies.
  // ---------------------------------------------------------------------------

  /**
   * For A : (Bag Int),
   *
   * - IDENTICAL_NODES
   *     (= A A)
   *     ---> true
   */
  BagsRewriteResponse preRewriteEqual(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - SUB_BAG
   *     (bag.subbag A B)
   *     ---> (= (bag.difference_subtract A B) (as bag.empty (Bag Int)))
   */
  BagsRewriteResponse rewriteSubBag(const TNode& n) const;

  /**
   * For x : Int and A : (Bag Int),
   *
   * - MEMBER
   *     (bag.member x A)
   *     ---> (>= (bag.count x A) 1)
   */
  BagsRewriteResponse rewriteMember(const TNode& n) const;

  /**
   * For x : Int,
   *
   * - BAG_MAKE_COUNT_NEGATIVE
   *     (bag x 0)
   *     ---> (as bag.empty (Bag Int))
   *
   *     (bag x (- 2))
   *     ---> (as bag.empty (Bag Int))
   */
  BagsRewriteResponse rewriteMakeBag(const TNode& n) const;

  /**
   * For x : Int,
   *
   * - COUNT_EMPTY
   *     (bag.count x (as bag.empty (Bag Int)))
   *     ---> 0
   * - COUNT_BAG_MAKE
   *     (bag.count x (bag x 3))
   *     ---> 3
   */
  BagsRewriteResponse rewriteBagCount(const TNode& n) const;

  /**
   * For x, c : Int and X : (Bag (Tuple Int Int Int)):
   *
   * - SETOF_BAG_MAKE
   *     (bag.setof (bag x 3))
   *     ---> (bag x 1)
   *
   *     (bag.setof (bag x c))
   *     ---> (bag x (ite (>= c 1) 1 0))
   * - SETOF_PROJECTION_SORT (rewriteSetofOfMap)
   *     (bag.setof
   *       (bag.map
   *         (lambda ((t (Tuple Int Int Int)))
   *           (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
   *         X))
   *     ---> (bag.map
   *            (lambda ((r (Tuple Int Int)))
   *              (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
   *            (bag.setof
   *              (bag.map
   *                (lambda ((t (Tuple Int Int Int)))
   *                  (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
   *                X)))
   */
  BagsRewriteResponse rewriteSetof(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - UNION_MAX_SAME_OR_EMPTY
   *     (bag.union_max A A)
   *     ---> A
   *
   *     (bag.union_max A (as bag.empty (Bag Int)))
   *     ---> A
   * - UNION_MAX_EMPTY
   *     (bag.union_max (as bag.empty (Bag Int)) A)
   *     ---> A
   * - UNION_MAX_UNION_LEFT, also for bag.union_max and (bag.union_disjoint B A)
   *     (bag.union_max A (bag.union_disjoint A B))
   *     ---> (bag.union_disjoint A B)
   * - UNION_MAX_UNION_RIGHT, also for bag.union_disjoint and
   *   (bag.union_max B A)
   *     (bag.union_max (bag.union_max A B) A)
   *     ---> (bag.union_max A B)
   */
  BagsRewriteResponse rewriteUnionMax(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - UNION_DISJOINT_EMPTY_RIGHT
   *     (bag.union_disjoint A (as bag.empty (Bag Int)))
   *     ---> A
   * - UNION_DISJOINT_EMPTY_LEFT
   *     (bag.union_disjoint (as bag.empty (Bag Int)) A)
   *     ---> A
   * - UNION_DISJOINT_MAX_MIN, also with the sides swapped
   *     (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B))
   *     ---> (bag.union_disjoint A B)
   */
  BagsRewriteResponse rewriteUnionDisjoint(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - INTERSECTION_EMPTY_LEFT
   *     (bag.inter_min (as bag.empty (Bag Int)) A)
   *     ---> (as bag.empty (Bag Int))
   * - INTERSECTION_EMPTY_RIGHT
   *     (bag.inter_min A (as bag.empty (Bag Int)))
   *     ---> (as bag.empty (Bag Int))
   * - INTERSECTION_SAME
   *     (bag.inter_min A A)
   *     ---> A
   * - INTERSECTION_SHARED_LEFT, also for bag.union_max and (bag.union_disjoint
   *   B A)
   *     (bag.inter_min A (bag.union_disjoint A B))
   *     ---> A
   * - INTERSECTION_SHARED_RIGHT, also for bag.union_disjoint and
   *   (bag.union_max B A)
   *     (bag.inter_min (bag.union_max A B) A)
   *     ---> A
   */
  BagsRewriteResponse rewriteIntersectionMin(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - SUBTRACT_RETURN_LEFT
   *     (bag.difference_subtract A (as bag.empty (Bag Int)))
   *     ---> A
   *
   *     (bag.difference_subtract (as bag.empty (Bag Int)) B)
   *     ---> (as bag.empty (Bag Int))
   * - SUBTRACT_SAME
   *     (bag.difference_subtract A A)
   *     ---> (as bag.empty (Bag Int))
   * - SUBTRACT_DISJOINT_SHARED_LEFT
   *     (bag.difference_subtract (bag.union_disjoint A B) A)
   *     ---> B
   * - SUBTRACT_DISJOINT_SHARED_RIGHT
   *     (bag.difference_subtract (bag.union_disjoint B A) A)
   *     ---> B
   * - SUBTRACT_FROM_UNION, also for bag.union_disjoint and (bag.union_max B A)
   *     (bag.difference_subtract A (bag.union_max A B))
   *     ---> (as bag.empty (Bag Int))
   * - SUBTRACT_MIN, also for (bag.inter_min B A)
   *     (bag.difference_subtract (bag.inter_min A B) A)
   *     ---> (as bag.empty (Bag Int))
   */
  BagsRewriteResponse rewriteDifferenceSubtract(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - REMOVE_RETURN_LEFT
   *     (bag.difference_remove A (as bag.empty (Bag Int)))
   *     ---> A
   *
   *     (bag.difference_remove (as bag.empty (Bag Int)) B)
   *     ---> (as bag.empty (Bag Int))
   * - REMOVE_SAME
   *     (bag.difference_remove A A)
   *     ---> (as bag.empty (Bag Int))
   * - REMOVE_FROM_UNION, also for bag.union_max and (bag.union_disjoint B A)
   *     (bag.difference_remove A (bag.union_disjoint A B))
   *     ---> (as bag.empty (Bag Int))
   * - REMOVE_MIN, also for (bag.inter_min B A)
   *     (bag.difference_remove (bag.inter_min A B) A)
   *     ---> (as bag.empty (Bag Int))
   */
  BagsRewriteResponse rewriteDifferenceRemove(const TNode& n) const;
  /**
   * For x : Int,
   *
   * - CHOOSE_BAG_MAKE
   *     (bag.choose (bag x 3))
   *     ---> x
   */
  BagsRewriteResponse rewriteChoose(const TNode& n) const;
  /**
   * For x : Int,
   *
   * - CARD_BAG_MAKE
   *     (bag.card (bag x 3))
   *     ---> 3
   */
  BagsRewriteResponse rewriteCard(const TNode& n) const;

  /**
   * For A, B : (Bag Int),
   *
   * - EQ_REFL
   *     (= (bag.union_disjoint A (as bag.empty (Bag Int))) A)
   *     ---> true
   * - EQ_CONST_FALSE
   *     (= (bag 1 2) (bag 1 3))
   *     ---> false
   * - EQ_SYM, the smaller node first
   *     (= B A)
   *     ---> (= A B)
   */
  BagsRewriteResponse postRewriteEqual(const TNode& n) const;

  /**
   * For x : Int, A, B : (Bag Int), X : (Bag (Tuple Int Int)),
   * Y : (Bag (Tuple Int (Nullable Int))) with column 1 NOT NULL (see
   * TableFacts), g = (lambda ((y Int)) (+ y 1)) and
   * h = (lambda ((z Int)) (* z 2)),
   *
   * - MAP_IDENTITY
   *     (bag.map
   *       (lambda ((t (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
   *       X)
   *     ---> X
   * - NOT_NULL_COLUMNS (assumeNonNull)
   *     (bag.map
   *       (lambda ((t (Tuple Int (Nullable Int))))
   *         (tuple (ite (nullable.is_some ((_ tuple.select 1) t))
   *                     (nullable.val ((_ tuple.select 1) t))
   *                     0)))
   *       Y)
   *     ---> (bag.map
   *            (lambda ((t (Tuple Int (Nullable Int))))
   *              (tuple (nullable.val ((_ tuple.select 1) t))))
   *            Y)
   * - MAP_CONST
   *     (bag.map g (bag 1 3))
   *     ---> (bag 2 3)
   * - MAP_BAG_MAKE
   *     (bag.map g (bag x 3))
   *     ---> (bag (+ x 1) 3)
   * - MAP_UNION_DISJOINT
   *     (bag.map g (bag.union_disjoint A B))
   *     ---> (bag.union_disjoint (bag.map g A) (bag.map g B))
   * - MAP_MAP (rewriteMapOfMap)
   *     (bag.map h (bag.map g A))
   *     ---> (bag.map (lambda ((y Int)) (* (+ y 1) 2)) A)
   * - AGGREGATE_DEAD_COLUMNS (rewriteAggregateDeadColumns), also with a filter
   *   between the map and the aggregate
   *     (bag.map
   *       (lambda ((r (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) r) ((_ tuple.select 2) r)))
   *       ((_ table.aggr 0)
   *         (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *           (tuple ((_ tuple.select 0) t)
   *                  (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                  (+ ((_ tuple.select 2) acc) 1)))
   *         (tuple 0 0 0)
   *         X))
   *     ---> (bag.map
   *            (lambda ((r (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
   *            ((_ table.aggr 0)
   *              (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *                (tuple ((_ tuple.select 0) t)
   *                       (+ ((_ tuple.select 1) acc) 1)))
   *              (tuple 0 0)
   *              X))
   * - MAP_EQUAL_COLUMNS, for
   *   P = (lambda ((s (Tuple Int Int)))
   *         (= ((_ tuple.select 0) s) ((_ tuple.select 1) s)))
   *     (bag.map
   *       (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
   *       (bag.filter P X))
   *     ---> (bag.map
   *            (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t)))
   *            (bag.filter P X))
   * - MAP_FIXED_COLUMNS (fixedColumns, readFixed), for
   *   Q = (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 1) s) 5))
   *     (bag.map
   *       (lambda ((t (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 0))
   *       (bag.filter Q X))
   *     ---> (bag.map
   *            (lambda ((t (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t) 5 0))
   *            (bag.filter Q X))
   * - CANONICAL_VARIABLE (canonicalLambda)
   *     (bag.map g A)
   *     ---> (bag.map (lambda ((t_N Int)) (+ t_N 1)) A)
   */
  BagsRewriteResponse postRewriteMap(const TNode& n) const;

  /**
   * For x : Int, A, B : (Bag Int), C : (Bag (Nullable Int)),
   * Y : (Bag (Tuple Int (Nullable Int))) with column 1 NOT NULL (see
   * TableFacts), p = (lambda ((y Int)) (> y 0)),
   * g = (lambda ((z Int)) (+ z 1)) and
   * b = (ite (nullable.is_some y)
   *          (nullable.some (> (nullable.val y) 3))
   *          (as nullable.null (Nullable Bool))):
   *
   * - NOT_NULL_COLUMNS (assumeNonNull)
   *     (bag.filter
   *       (lambda ((t (Tuple Int (Nullable Int))))
   *         (and (nullable.is_some ((_ tuple.select 1) t))
   *              (> ((_ tuple.select 0) t) 3)))
   *       Y)
   *     ---> (bag.filter
   *            (lambda ((t (Tuple Int (Nullable Int))))
   *              (> ((_ tuple.select 0) t) 3))
   *            Y)
   * - FILTER_TRUE
   *     (bag.filter (lambda ((y Int)) true) A)
   *     ---> A
   * - FILTER_FALSE
   *     (bag.filter (lambda ((y Int)) false) A)
   *     ---> (as bag.empty (Bag Int))
   *
   *     (bag.filter (lambda ((y Int)) (and (> y 3) (not (> y 3)))) A)
   *     ---> (as bag.empty (Bag Int))
   * - FILTER_NULLABLE_TRUTH (normalizeTruth)
   *     (bag.filter
   *       (lambda ((y (Nullable Int)))
   *         (and (nullable.is_some b) (nullable.val b)))
   *       C)
   *     ---> (bag.filter
   *            (lambda ((y (Nullable Int)))
   *              (and (nullable.is_some y) (> (nullable.val y) 3)))
   *            C)
   * - FILTER_CONFLICTING_CONSTANTS
   *     (bag.filter (lambda ((y Int)) (and (= y 1) (= y 2))) A)
   *     ---> (as bag.empty (Bag Int))
   *
   *     (bag.filter
   *       (lambda ((y (Nullable Int)))
   *         (and (nullable.is_some y) (= y (nullable.some 5))))
   *       C)
   *     ---> (bag.filter
   *            (lambda ((y (Nullable Int))) (= y (nullable.some 5)))
   *            C)
   * - CANONICAL_VARIABLE (canonicalLambda)
   *     (bag.filter p A)
   *     ---> (bag.filter (lambda ((t_N Int)) (> t_N 0)) A)
   * - FILTER_CONST
   *     (bag.filter p (bag.union_disjoint (bag 1 2) (bag (- 3) 1)))
   *     ---> (bag 1 2)
   * - FILTER_BAG_MAKE
   *     (bag.filter p (bag x 2))
   *     ---> (bag x (ite (> x 0) 2 0))
   * - FILTER_UNION_DISJOINT
   *     (bag.filter p (bag.union_disjoint A B))
   *     ---> (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   * - FILTER_MAP (rewriteFilterOfMap)
   *     (bag.filter p (bag.map g A))
   *     ---> (bag.map g (bag.filter (lambda ((z Int)) (> (+ z 1) 0)) A))
   */
  BagsRewriteResponse postRewriteFilter(const TNode& n) const;

  /**
   * For x, c : Int, A, B : (Bag Int) and p = (lambda ((y Int)) (> y 0)),
   *
   * - ALL_EMPTY
   *     (bag.all p (as bag.empty (Bag Int)))
   *     ---> true
   * - ALL_BAG_MAKE
   *     (bag.all p (bag x c))
   *     ---> (or (> x 0) (<= c 0))
   * - ALL_UNION_DISJOINT
   *     (bag.all p (bag.union_disjoint A B))
   *     ---> (and (bag.all p A) (bag.all p B))
   * - ALL_FILTER
   *     (bag.all p A)
   *     ---> (= (bag.filter p A) A)
   */
  BagsRewriteResponse postRewriteAll(TNode n);
  /**
   * For x, c : Int, A, B : (Bag Int) and p = (lambda ((y Int)) (> y 0)),
   *
   * - SOME_EMPTY
   *     (bag.some p (as bag.empty (Bag Int)))
   *     ---> false
   * - SOME_BAG_MAKE
   *     (bag.some p (bag x c))
   *     ---> (and (> c 0) (> x 0))
   * - SOME_UNION_DISJOINT
   *     (bag.some p (bag.union_disjoint A B))
   *     ---> (or (bag.some p A) (bag.some p B))
   * - SOME_FILTER
   *     (bag.some p A)
   *     ---> (not (= (bag.filter p A) (as bag.empty (Bag Int))))
   */
  BagsRewriteResponse postRewriteSome(TNode n);

  /**
   * For x : Int, A, B : (Bag Int), Y : (Bag (Tuple Int (Nullable Int))) with
   * column 1 NOT NULL (see TableFacts) and
   * f = (lambda ((y Int) (a Int)) (+ y a)),
   *
   * - FOLD_CONST
   *     (bag.fold f 0 (bag.union_disjoint (bag 3 2) (bag 4 1)))
   *     ---> 10
   * - FOLD_BAG
   *     (bag.fold f 0 (bag x 2))
   *     ---> (+ x (+ x 0))
   * - NOT_NULL_COLUMNS (assumeNonNull)
   *     (bag.fold
   *       (lambda ((t (Tuple Int (Nullable Int))) (a Int))
   *         (ite (nullable.is_some ((_ tuple.select 1) t)) (+ a 1) a))
   *       0
   *       Y)
   *     ---> (bag.fold
   *            (lambda ((t (Tuple Int (Nullable Int))) (a Int)) (+ a 1))
   *            0
   *            Y)
   * - FOLD_TUPLE (rewriteFoldOfTuple)
   *     (bag.fold
   *       (lambda ((y Int) (acc (Tuple Int Int)))
   *         (tuple (+ ((_ tuple.select 0) acc) y)
   *                (+ ((_ tuple.select 1) acc) 1)))
   *       (tuple 0 0)
   *       A)
   *     ---> (tuple (bag.fold (lambda ((y Int) (a Int)) (+ a y)) 0 A)
   *                 (bag.fold (lambda ((y Int) (a Int)) (+ a 1)) 0 A))
   * - FOLD_CONSTANT_STEP
   *     (bag.fold (lambda ((y Int) (a Int)) 7) 0 A)
   *     ---> (ite (= A (as bag.empty (Bag Int))) 0 7)
   * - FOLD_UNION_DISJOINT, the smaller node first
   *     (bag.fold f 0 (bag.union_disjoint A B))
   *     ---> (bag.fold f (bag.fold f 0 A) B)
   * - CANONICAL_VARIABLE (canonicalLambda)
   *     (bag.fold f 0 A)
   *     ---> (bag.fold (lambda ((t_N Int) (acc_N Int)) (+ t_N acc_N)) 0 A)
   */
  BagsRewriteResponse postRewriteFold(const TNode& n) const;
  /**
   * For r = (lambda ((a Int) (b Int)) (= (mod a 2) (mod b 2))),
   *
   * - PARTITION_CONST
   *     (bag.partition r (bag.union_disjoint (bag 1 1) (bag 2 1)))
   *     ---> (bag.union_disjoint (bag (bag 1 1) 1) (bag (bag 2 1) 1))
   */
  BagsRewriteResponse postRewritePartition(const TNode& n) const;
  /**
   * For X : (Bag (Tuple Int Int)), Y : (Bag (Tuple Int (Nullable Int))) with
   * column 1 NOT NULL (see TableFacts), the step of SUM(column 1)
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
   * and the step of COUNT(*)
   *   g = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1))),
   *
   * - NOT_NULL_COLUMNS (assumeNonNull)
   *     ((_ table.aggr 0)
   *       (lambda ((t (Tuple Int (Nullable Int))) (acc (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (ite (nullable.is_some ((_ tuple.select 1) t))
   *                     (+ ((_ tuple.select 1) acc) 1)
   *                     ((_ tuple.select 1) acc))))
   *       (tuple 0 0)
   *       Y)
   *     ---> ((_ table.aggr 0)
   *            (lambda ((t (Tuple Int (Nullable Int))) (acc (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t)
   *                     (+ ((_ tuple.select 1) acc) 1)))
   *            (tuple 0 0)
   *            Y)
   * - AGGREGATE_NO_KEYS
   *     (table.aggr f (tuple 0 0) X)
   *     ---> (bag (bag.fold f (tuple 0 0) X)
   *               (ite (= X (as bag.empty (Bag (Tuple Int Int)))) 0 1))
   * - AGGREGATE_CONSTANT_COLUMNS (rewriteAggregateConstantColumns)
   *     ((_ table.aggr 0)
   *       (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                7
   *                (+ ((_ tuple.select 2) acc) ((_ tuple.select 1) t))))
   *       (tuple 0 0 0)
   *       X)
   *     ---> (bag.map
   *            (lambda ((r (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) r) 7 ((_ tuple.select 1) r)))
   *            ((_ table.aggr 0) f (tuple 0 0) X))
   * - AGGREGATE_SORT_OUTPUT (rewriteAggregateSortOutput)
   *     ((_ table.aggr 0)
   *       (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *         (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t))
   *                ((_ tuple.select 0) t)))
   *       (tuple 0 0)
   *       X)
   *     ---> (bag.map
   *            (lambda ((r (Tuple Int Int)))
   *              (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
   *            ((_ table.aggr 0) f (tuple 0 0) X))
   * - CANONICAL_VARIABLE (canonicalLambda)
   *     ((_ table.aggr 0) g (tuple 0 0) X)
   *     ---> ((_ table.aggr 0)
   *            (lambda ((t_N (Tuple Int Int)) (acc_N (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t_N)
   *                     (+ ((_ tuple.select 1) acc_N) 1)))
   *            (tuple 0 0)
   *            X)
   * - AGGREGATE_MAP (rewriteAggregateOfMap)
   *     ((_ table.aggr 0)
   *       f
   *       (tuple 0 0)
   *       (bag.map
   *         (lambda ((t (Tuple Int Int)))
   *           (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
   *         X))
   *     ---> ((_ table.aggr 1)
   *            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *              (tuple ((_ tuple.select 1) t)
   *                     (+ ((_ tuple.select 1) acc) ((_ tuple.select 0) t))))
   *            (tuple 0 0)
   *            X)
   * - AGGREGATE_CONST
   *     ((_ table.aggr 0)
   *       f
   *       (tuple 0 0)
   *       (bag.union_disjoint (bag (tuple 1 2) 1) (bag (tuple 1 3) 1)))
   *     ---> (bag (tuple 1 5) 1)
   * - AGGREGATE_KEYED (keyedAggregateRows), with column 0 a key of X (see
   *   TableFacts)
   *     ((_ table.aggr 0) g (tuple 0 0) X)
   *     ---> (bag.map
   *            (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t) 1))
   *            X)
   */
  BagsRewriteResponse postRewriteAggregate(const TNode& n) const;
  /**
   * For X : (Bag (Tuple Int)),
   *
   * - PRODUCT_EMPTY
   *     (table.product X (as bag.empty (Bag (Tuple Int))))
   *     ---> (as bag.empty (Bag (Tuple Int Int)))
   */
  BagsRewriteResponse postRewriteProduct(const TNode& n) const;

  /**
   * For X : (Bag (Tuple Int Int)),
   *
   * - PROJECT_TO_MAP
   *     ((_ table.project 1 0) X)
   *     ---> (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.project 1 0) t))
   *                   X)
   */
  BagsRewriteResponse postRewriteProject(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // The normal form of select-project-join: maps above filters above
  // products. The functions compose lambdas only (see composable).
  // ---------------------------------------------------------------------------

  /** FILTER_MAP, see postRewriteFilter */
  BagsRewriteResponse rewriteFilterOfMap(const TNode& n) const;
  /** MAP_MAP, see postRewriteMap */
  BagsRewriteResponse rewriteMapOfMap(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // Aggregates ((_ table.aggr K) f i X): X grouped by its columns K, each
  // group folded by f from i. An empty X has no group.
  // ---------------------------------------------------------------------------

  /** AGGREGATE_MAP, see postRewriteAggregate and orderIndependentStep */
  BagsRewriteResponse rewriteAggregateOfMap(const TNode& n) const;
  /**
   * Whether the step f gives one value in any order of the rows, which
   * AGGREGATE_MAP needs. For same = {0}, nonNull = {} and
   * t, acc : (Tuple Int Int), true for the body of SUM(column 1)
   *
   *   (tuple ((_ tuple.select 0) t)
   *          (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))
   *
   * and false for the body that keeps the last column 1
   *
   *   (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t))
   */
  bool orderIndependentStep(const Node& f,
                            const std::set<uint32_t>& same,
                            const std::set<uint32_t>& nonNull) const;
  /** AGGREGATE_SORT_OUTPUT, see postRewriteAggregate */
  BagsRewriteResponse rewriteAggregateSortOutput(const TNode& n) const;
  /** FOLD_TUPLE, see postRewriteFold */
  BagsRewriteResponse rewriteFoldOfTuple(const TNode& n) const;
  /** AGGREGATE_DEAD_COLUMNS, see postRewriteMap */
  BagsRewriteResponse rewriteAggregateDeadColumns(const TNode& n) const;
  /** AGGREGATE_CONSTANT_COLUMNS, see postRewriteAggregate */
  BagsRewriteResponse rewriteAggregateConstantColumns(const TNode& n) const;
  /**
   * AGGREGATE_KEYED, see postRewriteAggregate: the map of A, or null when A's
   * group columns hold no key.
   */
  Node keyedAggregateRows(const Node& A) const;

  // ---------------------------------------------------------------------------
  // Sets, keys and semi-joins
  // ---------------------------------------------------------------------------

  /** SETOF_PROJECTION_SORT, see rewriteSetof */
  BagsRewriteResponse rewriteSetofOfMap(const TNode& n) const;
  /**
   * The keys of B. For X, Y : (Bag (Tuple Int Int)) with the key {0}:
   *
   *   X                          {{0}}
   *   (table.product X Y)        {{0, 2}}
   *   (bag.map
   *     (lambda ((t (Tuple Int Int)))
   *       (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
   *     X)                       {{1}}
   *   (bag.setof X)              {{0}, {0, 1}}
   */
  std::vector<std::set<uint32_t>> rowKeys(const Node& B) const;
  /**
   * The keys that the facts give the table constant B, also under filters:
   * {{0, 2}, {1}} for the keys {0, 2} and {1} (see TableFacts).
   */
  std::vector<std::set<uint32_t>> keysOf(const Node& B) const;

  // ---------------------------------------------------------------------------
  // Facts: keys and NOT NULL columns of table constants
  // ---------------------------------------------------------------------------

  /**
   * Adds to facts the key that the equality n states, and returns whether it
   * states one. The projection M onto the columns of the key is a set, with n
   * either way round. For X : (Bag (Tuple Int Int Int)), the key {0, 2} of X
   * from
   *
   *   n = (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
   *
   * and, as the rewriter of the theory leaves a key on columns out of order
   * (SETOF_PROJECTION_SORT), from
   *
   *   n = (= ((_ table.project 2 0) X)
   *          (bag.map
   *            (lambda ((r (Tuple Int Int)))
   *              (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
   *            (bag.setof ((_ table.project 0 2) X))))
   *
   * where the map only puts the columns back in order, so its image of a set
   * is a set. A projection may also be a bag.map of a projection lambda
   * (PROJECT_TO_MAP).
   */
  bool readKey(const TNode& n, TableFacts& facts) const;
  /**
   * Adds to facts the NOT NULL column that the equality n states, and returns
   * whether it states one. For X : (Bag (Tuple Int (Nullable Int))), column 1
   * of X from
   *
   *   n = (= (bag.filter
   *            (lambda ((t (Tuple Int (Nullable Int))))
   *              (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
   *            X)
   *          (as bag.empty (Bag (Tuple Int (Nullable Int)))))
   *
   * with both equalities either way round.
   */
  bool readNotNull(const TNode& n, TableFacts& facts) const;
  /**
   * Whether t is never null, for the never-null columns nx of the row x and
   * nacc of the accumulator acc; x and acc may be null. For
   * x : (Tuple Int (Nullable Int)), nx = {1} and y : (Nullable Int), true for
   *
   *   (ite (> ((_ tuple.select 0) x) 3)
   *        ((_ tuple.select 1) x)
   *        (nullable.some 0))
   *
   * and for ((_ tuple.select 0) x) : Int, false for y.
   */
  bool nonNullTerm(const Node& t,
                   const Node& x,
                   const std::set<uint32_t>& nx,
                   const Node& acc,
                   const std::set<uint32_t>& nacc) const;
  /**
   * The never-null columns of the aggregate B. For X : (Bag (Tuple Int Int)),
   * {0, 1} for
   *
   *   ((_ table.aggr 0)
   *     (lambda ((t (Tuple Int Int))
   *              (acc (Tuple (Nullable Int) (Nullable Int))))
   *       (tuple ((_ tuple.select 0) acc) (nullable.some 1)))
   *     (tuple (nullable.some 0) (as nullable.null (Nullable Int)))
   *     X)
   */
  std::set<uint32_t> aggregateNonNull(const Node& B) const;
  /**
   * The never-null columns of B. For
   * X : (Bag (Tuple (Nullable Int) (Nullable Int))) with column 0 NOT NULL,
   * {0, 1} for
   *
   *   (bag.filter
   *     (lambda ((t (Tuple (Nullable Int) (Nullable Int))))
   *       (nullable.is_some ((_ tuple.select 1) t)))
   *     X)
   *
   * Cached in d_nonNull.
   */
  std::set<uint32_t> nonNullColumns(const Node& B) const;
  /**
   * For x : (Tuple Int (Nullable Int)) and cols = {1},
   *
   *   (nullable.is_some ((_ tuple.select 1) x))
   *   ---> true
   *
   *   (= ((_ tuple.select 1) x) (as nullable.null (Nullable Int)))
   *   ---> false
   */
  Node assumeNonNull(const Node& body,
                     const Node& x,
                     const std::set<uint32_t>& cols) const;

  // ---------------------------------------------------------------------------
  // Columns that hold one constant in every row
  // ---------------------------------------------------------------------------

  /**
   * {1 -> 5} for
   * (lambda ((t (Tuple Int Int))) (and (= ((_ tuple.select 1) t) 5) q)).
   */
  std::map<uint32_t, Node> fixedColumns(const Node& p) const;
  /**
   * {1 -> 7} for the aggregate of AGGREGATE_CONSTANT_COLUMNS in
   * postRewriteAggregate.
   */
  std::map<uint32_t, Node> aggregateConstants(const Node& A) const;
  /**
   * For fixed = {1 -> 5},
   *
   *   (+ ((_ tuple.select 0) var) ((_ tuple.select 1) var))
   *   ---> (+ ((_ tuple.select 0) var) 5)
   */
  Node readFixed(const Node& body,
                 const Node& var,
                 const std::map<uint32_t, Node>& fixed) const;

  // ---------------------------------------------------------------------------
  // Emptiness tests and SQL's three-valued truth in lambda bodies
  // ---------------------------------------------------------------------------

  /**
   * (ite c b false) for
   * X = (ite c (nullable.some b) (as nullable.null (Nullable Bool))); null
   * when X is not such an ite.
   */
  Node truthOf(const Node& X) const;
  /**
   * FILTER_NULLABLE_TRUTH, see postRewriteFilter. For X with truthOf(X) = T,
   *
   *   (and (nullable.is_some X) (nullable.val X))
   *   ---> T
   */
  Node normalizeTruth(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Canonical lambdas: alpha-equivalent lambdas become one node
  // ---------------------------------------------------------------------------

  /** The variable accrow_N of an aggregate's accumulator of sort type */
  Node accumulatorVariable(TypeNode type) const;
  /**
   * CANONICAL_VARIABLE, for N the id of f's alpha key (see alphaKey):
   *
   *   (lambda ((s Int) (b Int)) (+ s b))
   *   ---> (lambda ((t_N Int) (acc_N Int)) (+ t_N acc_N))
   *
   * f's body is first simplified (see simplifyIteSame).
   */
  Node canonicalLambda(const Node& f) const;
  /**
   * One node for lambdas that differ only in the names of their variables:
   * (lambda ((s Int)) (+ s 1)) and (lambda ((y Int)) (+ 1 y)) have the same
   * key. Cached in d_alphaKeys.
   */
  Node alphaKey(const Node& f) const;
  /**
   * The alpha key of root, with bound mapping the variables of the binders
   * around root to their placeholders, at binding depth depth.
   */
  Node alphaKeyScope(TNode root,
                     std::unordered_map<TNode, Node>& bound,
                     size_t depth) const;
  /** the alpha keys computed so far */
  mutable std::unordered_map<Node, Node> d_alphaKeys;
  /** cache of nonNullColumns, cleared when a not-null fact is recorded */
  mutable std::unordered_map<Node, std::set<uint32_t>> d_nonNull;
  /**
   *   (ite (= a b) b a)
   *   ---> a
   *
   *   (ite (= a b) a b)
   *   ---> b
   */
  Node simplifyIteSame(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Lambdas and rows
  // ---------------------------------------------------------------------------

  /**
   * {2, 0} for
   *   (lambda ((t (Tuple Int Int Int)))
   *     (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
   * or (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 2 0) t)); empty
   * for any other f.
   */
  std::vector<uint32_t> projectionIndices(const Node& f) const;
  /**
   * For f = (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3)) and
   * x = (tuple a b),
   *
   *   (> ((_ tuple.select 1) (tuple a b)) 3)
   *
   * (f x) when f is not a lambda; null when the substitution would capture a
   * variable.
   */
  Node applyFunction(const Node& f, const Node& x) const;
  /** f as a lambda when it is a function array constant, else f */
  Node asLambda(const Node& f) const;
  /** whether v occurs free in n */
  bool occursFree(const Node& n, const Node& v) const;
  /** The one bound row variable of a tuple type, row_N */
  Node rowVariable(TypeNode tupleType) const;
  /** Whether a closure in body binds var */
  bool bindsVariable(const Node& body, const Node& var) const;
  /** The lambda of the variable var with the body body */
  Node mkLambda(const Node& var, const Node& body) const;
  /** whether f is a lambda of one variable, which the rules may compose */
  bool composable(const Node& f) const;
  /**
   * (t, (f t)) for a declared function f, with t the row variable of f's
   * argument sort; the variable and the body for a lambda.
   */
  std::pair<Node, Node> lambdaOf(const Node& f) const;
  /**
   * {0, 2} for the variable t and the body
   * (> ((_ tuple.select 0) t) ((_ tuple.select 2) t)); false when body uses
   * var other than through tuple.select.
   */
  bool readPositions(const Node& body,
                     const Node& var,
                     std::set<uint32_t>& positions) const;

 private:
  /** the integer constants 0 and 1 */
  Node d_zero;
  Node d_one;
  /**
   * Pointer to the rewriter. NOTE this is a cyclic dependency, and should
   * be removed.
   */
  Rewriter* d_rewriter;
  /** Reference to the rewriter statistics. */
  HistogramStat<Rewrite>* d_statistics;
  /** whether the logic has higher-order terms, see the constructor */
  bool d_higherOrder;
  /** the keys and NOT NULL columns of tables, null for none (TableFacts) */
  const TableFacts* d_facts;

}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H */
