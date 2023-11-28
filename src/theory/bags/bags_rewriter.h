/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H
#define CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H

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
  BagsRewriteResponse(const BagsRewriteResponse& r);
  /** the rewritten node */
  Node d_node;
  /** type of rewrite used by bags */
  Rewrite d_rewrite;

}; /* struct BagsRewriteResponse */

class BagsRewriter : public TheoryRewriter
{
 public:
  BagsRewriter(Rewriter* r, HistogramStat<Rewrite>* statistics = nullptr);

  /**
   * postRewrite nodes with kinds: BAG_MAKE, BAG_COUNT, BAG_UNION_MAX,
   * BAG_UNION_DISJOINT, BAG_INTER_MIN, BAG_DIFFERENCE_SUBTRACT,
   * BAG_DIFFERENCE_REMOVE, BAG_CHOOSE, BAG_CARD, BAG_IS_SINGLETON. See the
   * rewrite rules for these kinds below.
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * preRewrite nodes with kinds: EQUAL, BAG_SUBBAG, BAG_MEMBER.
   * See the rewrite rules for these kinds below.
   */
  RewriteResponse preRewrite(TNode n) override;

 private:
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
   * - (bag.count x bag.empty) = 0
   * - (bag.count x (bag x c)) = (ite (>= c 1) c 0)
   * - otherwise = n
   */
  BagsRewriteResponse rewriteBagCount(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.duplicate_removal (bag x n)) = (bag x 1)
   *     where n is a positive constant
   */
  BagsRewriteResponse rewriteDuplicateRemoval(const TNode& n) const;

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
   * - (bag.card (bag x c)) = c where c is a constant > 0
   * - otherwise = n
   */
  BagsRewriteResponse rewriteCard(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.is_singleton (bag x c)) = (c == 1)
   */
  BagsRewriteResponse rewriteIsSingleton(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.from_set (set.singleton x)) = (bag x 1)
   */
  BagsRewriteResponse rewriteFromSet(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.to_set (bag x n)) = (set.singleton x)
   *     where n is a positive constant and T is the type of the bag's elements
   */
  BagsRewriteResponse rewriteToSet(const TNode& n) const;

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
   */
  BagsRewriteResponse postRewriteMap(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
   *  - (bag.filter p (bag x y)) = (ite (p x) (bag x y) (as bag.empty (Bag T)))
   *  - (bag.filter p (bag.union_disjoint A B)) =
   *       (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   *  where p: T -> Bool
   */
  BagsRewriteResponse postRewriteFilter(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.fold f t (as bag.empty (Bag T1))) = t
   *  - (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, where n > 0
   *  - (bag.fold f t (bag.union_disjoint A B)) =
   *       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
   *  where f: T1 -> T2 -> T2
   */
  BagsRewriteResponse postRewriteFold(const TNode& n) const;
  BagsRewriteResponse postRewritePartition(const TNode& n) const;
  BagsRewriteResponse postRewriteAggregate(const TNode& n) const;
  /**
   *  rewrites for n include:
   *  - (bag.product A (as bag.empty T2)) = (as bag.empty T)
   *  - (bag.product (as bag.empty T2)) = (f t ... (f t (f t x))) n times, where
   * n > 0
   *  - (bag.fold f t (bag.union_disjoint A B)) =
   *       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
   *  where f: T1 -> T2 -> T2
   */
  BagsRewriteResponse postRewriteProduct(const TNode& n) const;

 private:
  /** Reference to the rewriter statistics. */
  NodeManager* d_nm;
  Node d_zero;
  Node d_one;
  /**
   * Pointer to the rewriter. NOTE this is a cyclic dependency, and should
   * be removed.
   */
  Rewriter* d_rewriter;
  /** Reference to the rewriter statistics. */
  HistogramStat<Rewrite>* d_statistics;
}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H */
