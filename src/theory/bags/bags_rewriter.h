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
 * The rewriter of the theory of bags and tables.
 *
 * Besides the rules for bag constants and the basic operators, it puts the
 * terms of relational algebra over tables (bags of tuples) in a normal form,
 * so that two queries that are one SQL rewrite apart become one term, or
 * terms that the solver relates cheaply. The normal form of a select-project-
 * join query is
 *   (bag.map h (bag.filter P (table.product X1 (table.product X2 ..))))
 * maps above filters above products, products right-nested and sorted, every
 * lambda over a canonical variable (canonicalLambda). Aggregates
 * ((_ table.aggr K) f i X) have their own normal forms: grouping by a key,
 * pushing through joins and unions, merging and splitting.
 *
 * Some rules use facts about the table constants of the problem, its keys and
 * NOT NULL columns, which the bags-facts preprocessing pass reads off the
 * top-level assertions (recordFacts).
 *
 * The notation of the examples is described at the top of bags_rewriter.cpp:
 * SMT-LIB terms over tables X, Y of rows of sort T, with t a row bound by a
 * lambda and acc an accumulator. Each rule is named by its Rewrite value,
 * see rewrites.h, and shown as
 *   previous node
 *   ---> next node
 */
class BagsRewriter : public TheoryRewriter
{
 public:
  /**
   * With higherOrder false, for a logic without higher-order terms, the rules
   * that build a lambda where the term has none do not apply, since the theory
   * of uninterpreted functions rejects lambdas there:
   * - FILTER_MAP, MAP_MAP and PROJECT_TO_MAP
   * The rewriter does not know the logic, so the default is false: the owner
   * of the rewriter passes true for a higher-order logic.
   */
  BagsRewriter(NodeManager* nm,
               Rewriter* r,
               HistogramStat<Rewrite>* statistics = nullptr,
               bool higherOrder = false);

  /**
   * postRewrite nodes with kinds: EQUAL, BAG_MAKE, BAG_COUNT, BAG_SETOF,
   * BAG_UNION_MAX, BAG_UNION_DISJOINT, BAG_INTER_MIN,
   * BAG_DIFFERENCE_SUBTRACT, BAG_DIFFERENCE_REMOVE, BAG_CHOOSE, BAG_CARD,
   * BAG_MAP, BAG_FILTER, BAG_ALL, BAG_SOME, BAG_FOLD, BAG_PARTITION,
   * TABLE_PRODUCT, TABLE_PROJECT and TABLE_AGGREGATE; a node
   * whose children are constants is evaluated. See the rewrite rules for
   * these kinds below.
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * preRewrite nodes with kinds: EQUAL, BAG_SUBBAG, BAG_MEMBER.
   * See the rewrite rules for these kinds below.
   */
  RewriteResponse preRewrite(TNode n) override;

  /**
   * Record the facts a top-level assertion states about table constants,
   * which the rules below then use: the keys of a table (see recordKey) and
   * its NOT NULL columns (see recordNotNull). Conjuncts of a top-level
   * conjunction are read too. The bags-facts preprocessing pass calls this on
   * every assertion before any of them is rewritten; the rewriter never
   * reads a fact off an equality it rewrites, which may not be asserted (it
   * may occur under a negation). E.g. for the assertions
   *   (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X))
   *   (= (bag.filter (lambda ((t T))
   *                    (= ((_ tuple.select 1) t)
   *                       (as nullable.null (Nullable Int))))
   *                  X)
   *      (as bag.empty (Bag T)))
   * column 0 is a key of X and column 1 of X is never null.
   */
  void recordFacts(TNode assertion) const;

 private:
  // ---------------------------------------------------------------------------
  // The rules of each kind. A function returns its argument with
  // Rewrite::NONE when no rule applies.
  // ---------------------------------------------------------------------------

  /**
   * rewrites for n include:
   * - (= A A) = true where A is a bag
   */
  BagsRewriteResponse preRewriteEqual(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.subbag A B) = ((bag.difference_subtract A B) == bag.empty)
   */
  BagsRewriteResponse rewriteSubBag(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.member x A) = (>= (bag.count x A) 1)
   */
  BagsRewriteResponse rewriteMember(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag x 0) = (bag.empty T) where T is the type of x
   * - (bag x (-c)) = (bag.empty T) where T is the type of x, and c > 0 is a
   *   constant
   * - otherwise = n
   */
  BagsRewriteResponse rewriteMakeBag(const TNode& n) const;

  /**
   * rewrites for n include:
   * - COUNT_EMPTY: (bag.count x (as bag.empty (Bag T))) ---> 0
   * - COUNT_BAG_MAKE: (bag.count x (bag x c)) ---> c, c > 0 a constant
   */
  BagsRewriteResponse rewriteBagCount(const TNode& n) const;

  /**
   * rewrites for n include, unless n is the bag.setof of a key assertion
   * (see BagsKeyTermAttribute in the .cpp):
   * - SETOF_BAG_MAKE: (bag.setof (bag x c)) ---> (bag x 1), c > 0 a
   *   constant; (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
   * - SETOF_PROJECTION_SORT, see rewriteSetofOfMap
   */
  BagsRewriteResponse rewriteSetof(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.union_max A bag.empty) = A
   * - (bag.union_max bag.empty A) = A
   * - (bag.union_max A A) = A
   * - (bag.union_max A (bag.union_max A B)) = (bag.union_max A B)
   * - (bag.union_max A (bag.union_max B A)) = (bag.union_max B A)
   * - (bag.union_max (bag.union_max A B) A) = (bag.union_max A B)
   * - (bag.union_max (bag.union_max B A) A) = (bag.union_max B A)
   * - (bag.union_max A (bag.union_disjoint A B)) = (bag.union_disjoint A B)
   * - (bag.union_max A (bag.union_disjoint B A)) = (bag.union_disjoint B A)
   * - (bag.union_max (bag.union_disjoint A B) A) = (bag.union_disjoint A B)
   * - (bag.union_max (bag.union_disjoint B A) A) = (bag.union_disjoint B A)
   * - otherwise = n
   */
  BagsRewriteResponse rewriteUnionMax(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.union_disjoint A bag.empty) = A
   * - (bag.union_disjoint bag.empty A) = A
   * - (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B)) =
   *         (bag.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
   * - other permutations of the above like swapping A and B, or swapping
   *   bag.intersection_min and bag.union_max
   * - otherwise = n
   */
  BagsRewriteResponse rewriteUnionDisjoint(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.inter_min A bag.empty) = bag.empty
   * - (bag.inter_min bag.empty A) = bag.empty
   * - (bag.inter_min A A) = A
   * - (bag.inter_min A (bag.union_disjoint A B)) = A
   * - (bag.inter_min A (bag.union_disjoint B A)) = A
   * - (bag.inter_min (bag.union_disjoint A B) A) = A
   * - (bag.inter_min (bag.union_disjoint B A) A) = A
   * - (bag.inter_min A (bag.union_max A B)) = A
   * - (bag.inter_min A (bag.union_max B A)) = A
   * - (bag.inter_min (bag.union_max A B) A) = A
   * - (bag.inter_min (bag.union_max B A) A) = A
   * - otherwise = n
   */
  BagsRewriteResponse rewriteIntersectionMin(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.difference_subtract A bag.empty) = A
   * - (bag.difference_subtract bag.empty A) = bag.empty
   * - (bag.difference_subtract A A) = bag.empty
   * - (bag.difference_subtract (bag.union_disjoint A B) A) = B
   * - (bag.difference_subtract (bag.union_disjoint B A) A) = B
   * - (bag.difference_subtract A (bag.union_disjoint A B)) = bag.empty
   * - (bag.difference_subtract A (bag.union_disjoint B A)) = bag.empty
   * - (bag.difference_subtract A (bag.union_max A B)) = bag.empty
   * - (bag.difference_subtract A (bag.union_max B A)) = bag.empty
   * - (bag.difference_subtract (bag.inter_min A B) A) = bag.empty
   * - (bag.difference_subtract (bag.inter_min B A) A) = bag.empty
   * - otherwise = n
   */
  BagsRewriteResponse rewriteDifferenceSubtract(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.difference_remove A bag.empty) = A
   * - (bag.difference_remove bag.empty A) = bag.empty
   * - (bag.difference_remove A A) = bag.empty
   * - (bag.difference_remove A (bag.union_disjoint A B)) = bag.empty
   * - (bag.difference_remove A (bag.union_disjoint B A)) = bag.empty
   * - (bag.difference_remove A (bag.union_max A B)) = bag.empty
   * - (bag.difference_remove A (bag.union_max B A)) = bag.empty
   * - (bag.difference_remove (bag.inter_min A B) A) = bag.empty
   * - (bag.difference_remove (bag.inter_min B A) A) = bag.empty
   * - otherwise = n
   */
  BagsRewriteResponse rewriteDifferenceRemove(const TNode& n) const;
  /**
   * rewrites for n include:
   * - (bag.choose (bag x c)) = x where c is a constant > 0
   * - otherwise = n
   */
  BagsRewriteResponse rewriteChoose(const TNode& n) const;
  /**
   * rewrites for n include:
   * - (bag.card (bag x c)) = c where c is a constant
   * - otherwise = n
   */
  BagsRewriteResponse rewriteCard(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (= A A) = true
   *  - (= A B) = false if A and B are different bag constants
   *  - (= B A) = (= A B) if A < B and at least one of A or B is not a constant
   */
  BagsRewriteResponse postRewriteEqual(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.map f (as bag.empty (Bag T1)) = (as bag.empty (Bag T2))
   *  - (bag.map f (bag x y)) = (bag (apply f x) y)
   *  - (bag.map f (bag.union_disjoint A B)) =
   *       (bag.union_disjoint (bag.map f A) (bag.map f B))
   *  where f: T1 -> T2
   *  - MAP_IDENTITY:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
   *                                      ((_ tuple.select 1) t)))
   *               X)
   *      ---> X
   *  - NOT_NULL_COLUMNS, the null tests of columns X never has null in are
   *    decided (see assumeNonNull):
   *      (bag.map (lambda ((t T))
   *                 (ite (nullable.is_some ((_ tuple.select 1) t)) a b))
   *               X)
   *      ---> (bag.map (lambda ((t T)) (ite true a b)) X)
   *  - MAP_MAP, see rewriteMapOfMap
   *  - AGGREGATE_DEAD_COLUMNS (rewriteAggregateDeadColumns)
   *  - MAP_EQUAL_COLUMNS, the first of the columns the filter equates:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)))
   *               (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                              ((_ tuple.select 2) s)))
   *                           X))
   *      ---> (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
   *                    (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                                   ((_ tuple.select 2) s)))
   *                                X))
   *  - MAP_FIXED_COLUMNS, the constants the filter fixes columns to:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)))
   *               (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5))
   *                           X))
   *      ---> (bag.map (lambda ((t T)) (tuple 5))
   *                    (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s)
   *                                                   5))
   *                                X))
   *    and, over an aggregate whose counter the filter tests, the constants
   *    its groups compute (see reachedGroupConstants)
   *  - CANONICAL_VARIABLE, see canonicalLambda
   */
  BagsRewriteResponse postRewriteMap(const TNode& n) const;

  /**
   *  rewrites for n include, unless n is the filter of a not-null assertion
   *  (see BagsKeyTermAttribute in the .cpp):
   *  - (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
   *  - FILTER_BAG_MAKE: (bag.filter p (bag x y)) ---> (bag x (ite (p x) y 0))
   *  - (bag.filter p (bag.union_disjoint A B)) =
   *       (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   *  where p: T -> Bool
   *  - NOT_NULL_COLUMNS, as for bag.map
   *  - FILTER_TRUE and FILTER_FALSE:
   *      (bag.filter (lambda ((t T)) true) A) ---> A
   *      (bag.filter (lambda ((t T)) false) A) ---> (as bag.empty (Bag T))
   *      (bag.filter (lambda ((t T)) (and p (not p))) A)
   *      ---> (as bag.empty (Bag T))
   *  - FILTER_NULLABLE_TRUTH, see normalizeTruth
   *  - FILTER_CONFLICTING_CONSTANTS:
   *      (bag.filter (lambda ((t T)) (and (= ((_ tuple.select 0) t) 1)
   *                                       (= ((_ tuple.select 0) t) 2)))
   *                  X)
   *      ---> (as bag.empty (Bag T))
   *    and the conjuncts the others imply go: (nullable.is_some a) beside
   *    (= a (nullable.some 5)), the null test of a value that a membership
   *    puts in a never-null column, (>= (* a b) 1) beside (>= a 1) and
   *    (>= b 1)
   *  - CANONICAL_VARIABLE, see canonicalLambda
   *  - FILTER_MAP, see rewriteFilterOfMap
   *  - AGGREGATE_KEYED, see keyedAggregateRows: under a filter that drops the
   *    row of initial values (see rejectsInitialRow),
   *      (bag.filter Q ((_ table.aggr 0) (lambda ((t T) (acc S)) b) i X))
   *      ---> (bag.filter Q (bag.map (lambda ((t T)) b[acc := i]) X))
   *    for 0 a key of X, and for an aggregate component of a product whose
   *    groups the filter keeps reached ones of (see reachedComponents)
   */
  BagsRewriteResponse postRewriteFilter(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.all p (as bag.empty (Bag T)) is rewritten as true
   *  - (bag.all p (bag x n)) is rewritten as ((p x) or (<= n 0))
   *  - (bag.all p (bag.union_disjoint A B)) is rewritten as
   *       (and (bag.all p A) (bag.all p B))
   *  - otherwise (bag.all p A) is rewritten as (= (bag.filter p A) A)
   *  where p: T -> Bool
   */
  BagsRewriteResponse postRewriteAll(TNode n);
  /**
   *  rewrites for n include:
   *  - (bag.some p (as bag.empty (Bag T)) is rewritten as false
   *  - (bag.some p (bag x n)) is rewritten as (and (> n 0) (p x))
   *  - (bag.some p (bag.union A B)) is rewritten as
   *       (or (bag.some p A) (bag.some p B))
   *  - otherwise (bag.some p A) is rewritten as
   *       (distinct (bag.filter p A) (as bag.empty (Bag T)))
   *  where p: T -> Bool
   */
  BagsRewriteResponse postRewriteSome(TNode n);

  /**
   *  rewrites for n include:
   *  - (bag.fold f t (as bag.empty (Bag T1))) = t
   *  - (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, where n > 0
   *  - (bag.fold f t (bag.union_disjoint A B)) =
   *       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
   *  where f: T1 -> T2 -> T2
   *  - NOT_NULL_COLUMNS, as for bag.map
   *  - FOLD_TUPLE, see rewriteFoldOfTuple
   *  - FOLD_CONSTANT_STEP:
   *      (bag.fold (lambda ((t T) (acc S)) c) i X)
   *      ---> (ite (= X (as bag.empty (Bag T))) i c)
   *    for c reading neither t nor acc
   *  - CANONICAL_VARIABLE, see canonicalLambda
   */
  BagsRewriteResponse postRewriteFold(const TNode& n) const;
  /**
   * rewrites for n include:
   * - PARTITION_CONST: a bag.partition of a constant bag is evaluated
   */
  BagsRewriteResponse postRewritePartition(const TNode& n) const;
  /**
   * rewrites for n = ((_ table.aggr K) f i X) include:
   * - NOT_NULL_COLUMNS, as for bag.map, in the steps of f
   * - AGGREGATE_NO_KEYS, one group of all of X, even an empty X:
   *     ((_ table.aggr) f i X) ---> (bag (bag.fold f i X) 1)
   * - AGGREGATE_SORT_OUTPUT, see rewriteAggregateSortOutput
   * - AGGREGATE_MAP, see rewriteAggregateOfMap
   * - CANONICAL_VARIABLE, see canonicalLambda
   * - AGGREGATE_CONST: an aggregate of constants is evaluated
   */
  BagsRewriteResponse postRewriteAggregate(const TNode& n) const;
  /**
   * rewrites for n include:
   * - PRODUCT_EMPTY:
   *     (table.product X (as bag.empty (Bag U))) ---> (as bag.empty (Bag V))
   *   and the same on the left
   */
  BagsRewriteResponse postRewriteProduct(const TNode& n) const;

  /**
   * PROJECT_TO_MAP: a projection is a map, which the map rules then reach:
   *   ((_ table.project 1 0) X)
   *   ---> (bag.map (lambda ((t T)) ((_ tuple.project 1 0) t)) X)
   */
  BagsRewriteResponse postRewriteProject(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // The normal form of select-project-join: maps above filters above
  // products. The functions compose lambdas only (see composable); a declared
  // function symbol is left to the rules above.
  // ---------------------------------------------------------------------------

  /**
   * FILTER_MAP:
   *   (bag.filter (lambda ((s U)) p) (bag.map (lambda ((t T)) e) A))
   *   ---> (bag.map (lambda ((t T)) e)
   *                 (bag.filter (lambda ((t T)) p[s := e]) A))
   */
  BagsRewriteResponse rewriteFilterOfMap(const TNode& n) const;
  /**
   * MAP_MAP:
   *   (bag.map (lambda ((s U)) e) (bag.map (lambda ((t T)) g) A))
   *   ---> (bag.map (lambda ((t T)) e[s := g]) A)
   */
  BagsRewriteResponse rewriteMapOfMap(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // Aggregates ((_ table.aggr K) f i X): X grouped by its columns K, each
  // group folded by f from i. The translator adds a counter column to every
  // aggregate with group columns, (+ ((_ tuple.select c) acc) 1) from 0,
  // under a filter that tests it positive: SQL's GROUP BY makes no group of
  // an empty table, while table.aggr folds it to the row of initial values i.
  // ---------------------------------------------------------------------------

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
  BagsRewriteResponse rewriteAggregateOfMap(const TNode& n) const;
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
  BagsRewriteResponse rewriteAggregateSortOutput(const TNode& n) const;
  /**
   * FOLD_TUPLE, a fold of tuples whose components read their own
   * accumulator only:
   *   (bag.fold (lambda ((t T) (acc (Tuple Int Int))) (tuple b0 b1))
   *             (tuple i0 i1) X)
   *   ---> (tuple (bag.fold (lambda ((t T) (a Int)) b0') i0 X)
   *               (bag.fold (lambda ((t T) (a Int)) b1') i1 X))
   */
  BagsRewriteResponse rewriteFoldOfTuple(const TNode& n) const;
  /**
   * AGGREGATE_DEAD_COLUMNS, a column of the aggregate nothing reads:
   *   (bag.map h ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 a1 a2))
   *                                (tuple i0 i1 i2) X))
   *   ---> (bag.map h' ((_ table.aggr 0) (lambda ((t T) (acc S'))
   *                                        (tuple a0 a2'))
   *                                      (tuple i0 i2) X))
   * also under a filter between the map and the aggregate
   */
  BagsRewriteResponse rewriteAggregateDeadColumns(const TNode& n) const;
  /**
   * For A = ((_ table.aggr K) f i X) with K containing a key of X (see
   * rowKeys): the rows of the groups some row reached, every group one row
   * of X folded once,
   *   (bag.map (lambda ((t T)) b[acc := i]) X)
   * for f = (lambda ((t T) (acc S)) b); null otherwise. They are the
   * aggregate's rows but for the row of initial values of an empty X, so
   * AGGREGATE_KEYED uses them where that row is dropped.
   */
  Node keyedAggregateRows(const Node& A) const;
  /** Whether n, a formula, rewrites to false */
  bool rewritesToFalse(const Node& n) const;
  /**
   * Whether the predicate P is false on the row of initial values i, the one
   * row an aggregate of an empty table has: (P i) rewrites to false, as for
   *   P = (lambda ((r V)) (>= ((_ tuple.select 2) r) 1))
   *   i = (tuple (as nullable.null (Nullable Int)) (nullable.some 0) 0)
   */
  bool rejectsInitialRow(const Node& P, const Node& i) const;

  // ---------------------------------------------------------------------------
  // Sets, keys and semi-joins
  // ---------------------------------------------------------------------------

  /**
   * SETOF_PROJECTION_SORT, the set of a map that projects onto columns in
   * another order than theirs:
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
  BagsRewriteResponse rewriteSetofOfMap(const TNode& n) const;
  /**
   * The keys of B read off its structure: a table's declared keys, kept by
   * filters, intersections and differences, by maps that keep their columns,
   * and combined by products; all the columns of a bag.setof; the group
   * columns an aggregate's rows copy. With the key {0} of X and of Y, and X
   * of two columns, (table.product X Y) has the key {0, 2}. Every key found
   * makes B a set.
   */
  std::vector<std::set<uint32_t>> rowKeys(const Node& B) const;
  /**
   * The keys of a table constant (see BagsKeysAttribute in the .cpp), or of
   * a filter over one: {{0, 2}, {1}} for keys {0, 2} and {1}.
   */
  std::vector<std::set<uint32_t>> keysOf(const Node& B) const;

  // ---------------------------------------------------------------------------
  // Facts: keys and NOT NULL columns of table constants
  // ---------------------------------------------------------------------------

  /**
   * Record the key a key assertion states: for n =
   *   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
   * either way round, or with the projection as a bag.map, X gets the key
   * {0, 2} (see BagsKeysAttribute in the .cpp), and the assertion's bag.setof
   * is not rewritten (BagsKeyTermAttribute). Called for top-level assertions
   * only, see recordFacts.
   */
  void recordKey(const TNode& n) const;
  /**
   * Record the never-null column a not-null assertion states: for n =
   *   (= (bag.filter (lambda ((t T))
   *                    (= (as nullable.null (Nullable Int))
   *                       ((_ tuple.select 1) t)))
   *                  X)
   *      (as bag.empty (Bag T)))
   * either way round, column 1 of X is never null (BagsNotNullAttribute in
   * the .cpp), and the filter is not rewritten (BagsKeyTermAttribute).
   * Called for top-level assertions only, see recordFacts.
   */
  void recordNotNull(const TNode& n) const;
  /**
   * Whether t is never null, given the columns nx of the row x and nacc of
   * the accumulator acc that are never null: true for (nullable.some a), for
   * ((_ tuple.select k) x) with k in nx, for an ite of such terms, and for a
   * fold seeded with (nullable.some a) whose step keeps it so. x and acc may
   * be null.
   */
  bool nonNullTerm(const Node& t,
                   const Node& x,
                   const std::set<uint32_t>& nx,
                   const Node& acc,
                   const std::set<uint32_t>& nacc) const;
  /**
   * The never-null columns of the rows of the aggregate B: those whose seed
   * is never null and whose step keeps them so; with reached, for the groups
   * a row reached, also those the step makes never null from these.
   */
  std::set<uint32_t> aggregateNonNull(const Node& B, bool reached) const;
  /**
   * The columns of B's rows that are never null, read off its structure:
   * the NOT NULL columns of a table constant, kept by filters, maps, unions
   * (of both sides), products, aggregates (see aggregateNonNull), and those a
   * filter tests with (nullable.is_some ((_ tuple.select k) t)). Cached in
   * d_nonNull.
   */
  std::set<uint32_t> nonNullColumns(const Node& B) const;
  /**
   * body with the null tests of the never-null columns cols of x decided:
   * with cols {1},
   *   (and (nullable.is_some ((_ tuple.select 1) x)) p) is (and true p)
   *   (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x)) is false
   */
  Node assumeNonNull(const Node& body,
                     const Node& x,
                     const std::set<uint32_t>& cols) const;

  // ---------------------------------------------------------------------------
  // Counters, steps of aggregates, and the groups a row reached
  // ---------------------------------------------------------------------------

  /**
   * The column c of the rows of an aggregate ((_ table.aggr K) f i X) that
   * counts the rows of each group, (+ ((_ tuple.select c) acc) 1) from 0,
   * when the filter predicate P has the conjunct
   * (>= ((_ tuple.select c) r) 1); -1 otherwise.
   */
  int counterColumn(const Node& P, const Node& f, const Node& i) const;
  /**
   * For a filter P over the product of comps, whose columns start at starts:
   * per component, the conjunct of P that tests its counter positive (-1
   * when none), in test, and whether its groups are reached: 1 when tested,
   * 2 when joined on all its group columns with a reached aggregate whose
   * input has the same key values, 0 otherwise. The rows of initial values
   * of a reached component are in no row that passes P.
   */
  std::vector<int> reachedComponents(const Node& P,
                                     const std::vector<Node>& comps,
                                     const std::vector<size_t>& starts,
                                     std::vector<int>& test) const;
  /**
   * The columns a filter predicate fixes to constants: {1 -> 5} for
   * (lambda ((t T)) (and (= ((_ tuple.select 1) t) 5) q)).
   */
  std::map<uint32_t, Node> fixedColumns(const Node& p) const;
  /**
   * The constant columns of the groups a counter filter F over an aggregate
   * keeps: those its step sets to a constant, and those it keeps at their
   * constant seed.
   */
  std::map<uint32_t, Node> reachedGroupConstants(const Node& F) const;
  /**
   * body with the columns of var that fixed maps read as their constants:
   * ((_ tuple.select 1) var) read as 5 for {1 -> 5}.
   */
  Node readFixed(const Node& body,
                 const Node& var,
                 const std::map<uint32_t, Node>& fixed) const;

  // ---------------------------------------------------------------------------
  // Emptiness tests and SQL's three-valued truth in lambda bodies
  // ---------------------------------------------------------------------------

  /**
   * The formula X = (nullable.some true) for a nullable Boolean X built of
   * ites over (nullable.some b) and null, or null when X is not one: (ite c b
   * false) for X = (ite c (nullable.some b) (as nullable.null (Nullable
   * Bool))).
   */
  Node truthOf(const Node& X) const;
  /**
   * FILTER_NULLABLE_TRUTH: body with the conjuncts (nullable.is_some X) and
   * (nullable.val X) replaced by truthOf(X), the one formula they say.
   */
  Node normalizeTruth(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Canonical lambdas: one variable per role and type, named after the
  // lambda's alpha key, so that alpha-equivalent lambdas are one node, which
  // the solver purifies into one function symbol
  // ---------------------------------------------------------------------------

  /** The variable of the accumulator of an aggregate's function, per type */
  Node accumulatorVariable(TypeNode type) const;
  /**
   * CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N the
   * id of f's alpha key, when that is safe:
   *   (lambda ((s T)) (> ((_ tuple.select 0) s) 3))
   *   ---> (lambda ((t_N T)) (> ((_ tuple.select 0) t_N) 3))
   * f's body is first simplified, see simplifyIteSame.
   */
  Node canonicalLambda(const Node& f) const;
  /**
   * A node equal for alpha-equivalent f: f with every variable it binds
   * replaced by a placeholder for its binding depth, every free variable by
   * one placeholder per type, the arguments of commutative operators sorted
   * and arithmetic atoms oriented over the placeholders. Cached in
   * d_alphaKeys.
   */
  Node alphaKey(const Node& f) const;
  /**
   * The alpha key of root, with bound mapping the variables of the binders
   * that enclose root to their placeholders, at binding depth depth.
   */
  Node alphaKeyScope(TNode root,
                     std::unordered_map<TNode, Node>& bound,
                     size_t depth) const;
  /** the alpha keys computed so far */
  mutable std::unordered_map<Node, Node> d_alphaKeys;
  /** cache of nonNullColumns, cleared when a not-null fact is recorded */
  mutable std::unordered_map<Node, std::set<uint32_t>> d_nonNull;
  /**
   * body with (ite (= a b) b a) replaced by a and (ite (= a b) a b) by b,
   * which the translator's null-aware steps leave once an accumulator is
   * known.
   */
  Node simplifyIteSame(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Lambdas and rows
  // ---------------------------------------------------------------------------

  /**
   * The columns a projection lambda selects, in order: {2, 0} for
   * (lambda ((t T)) (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t))) or
   * (lambda ((t T)) ((_ tuple.project 2 0) t)); empty when f is not one.
   */
  std::vector<uint32_t> projectionIndices(const Node& f) const;
  /**
   * (f x) beta-reduced: (> ((_ tuple.select 1) (tuple a b)) 3), which the
   * rewriter simplifies to (> b 3), for f = (lambda ((s T))
   * (> ((_ tuple.select 1) s) 3)) and x = (tuple a b); (f x) as an
   * application when f is not a lambda; null when the substitution would
   * capture a variable.
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
  /** (lambda ((var T)) body) */
  Node mkLambda(const Node& var, const Node& body) const;
  /** whether f is a lambda of one variable, which the rules may compose */
  bool composable(const Node& f) const;
  /**
   * The variable and body of the lambda (lambda ((t T)) body) a function of
   * type T -> S stands for: the lambda's own, or the row variable t of T and
   * (f t) for a function that is not a lambda.
   */
  std::pair<Node, Node> lambdaOf(const Node& f) const;
  /**
   * The tuple positions a lambda body reads of its bound variable, as
   * (_ tuple.select i) applications: {0, 2} for (> ((_ tuple.select 0) t)
   * ((_ tuple.select 2) t)); false when the variable is used any other way.
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

}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H */
