/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Kshitij Bansal, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__THEORY_SETS_REWRITER_H
#define CVC5__THEORY__SETS__THEORY_SETS_REWRITER_H

#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

class TheorySetsRewriter : public TheoryRewriter
{
 public:
  /**
   * Rewrite a node into the normal form for the theory of sets.
   * Called in post-order (really reverse-topological order) when
   * traversing the expression DAG during rewriting.  This is the
   * main function of the rewriter, and because of the ordering,
   * it can assume its children are all rewritten already.
   *
   * This function can return one of three rewrite response codes
   * along with the rewritten node:
   *
   *   REWRITE_DONE indicates that no more rewriting is needed.
   *   REWRITE_AGAIN means that the top-level expression should be
   *     rewritten again, but that its children are in final form.
   *   REWRITE_AGAIN_FULL means that the entire returned expression
   *     should be rewritten again (top-down with preRewrite(), then
   *     bottom-up with postRewrite()).
   *
   * Even if this function returns REWRITE_DONE, if the returned
   * expression belongs to a different theory, it will be fully
   * rewritten by that theory's rewriter.
   */
  RewriteResponse postRewrite(TNode node) override;

  /**
   * Rewrite a node into the normal form for the theory of sets
   * in pre-order (really topological order)---meaning that the
   * children may not be in the normal form.  This is an optimization
   * for theories with cancelling terms (e.g., 0 * (big-nasty-expression)
   * in arithmetic rewrites to 0 without the need to look at the big
   * nasty expression).  Since it's only an optimization, the
   * implementation here can do nothing.
   */
  RewriteResponse preRewrite(TNode node) override;

  /**
   * Rewrite an equality, in case special handling is required.
   */
  Node rewriteEquality(TNode equality)
  {
    // often this will suffice
    return postRewrite(equality).d_node;
  }

 private:
  /**
   * Returns true if elementTerm is in setTerm, where both terms are constants.
   */
  bool checkConstantMembership(TNode elementTerm, TNode setTerm);
  /**
   * Rewrite set comprehension
   */
  RewriteResponse postRewriteComprehension(TNode n);
  /**
   *  rewrites for n include:
   *  - (set.map f (as set.empty (Set T1)) = (as set.empty (Set T2))
   *  - (set.map f (set.singleton x)) = (set.singleton (apply f x))
   *  - (set.map f (set.union A B)) =
   *       (set.union (set.map f A) (set.map f B))
   *  where f: T1 -> T2
   */
  RewriteResponse postRewriteMap(TNode n);

  /**
   *  rewrites for n include:
   *  - (set.filter p (as set.empty (Set T)) = (as set.empty (Set T))
   *  - (set.filter p (set.singleton x)) =
   *       (ite (p x) (set.singleton x) (as set.empty (Set T)))
   *  - (set.filter p (set.union A B)) =
   *       (set.union (set.filter p A) (set.filter p B))
   *  where p: T -> Bool
   */
  RewriteResponse postRewriteFilter(TNode n);
  /**
   *  rewrites for n include:
   *  - (set.fold f t (as set.empty (Set T))) = t
   *  - (set.fold f t (set.singleton x)) = (f t x)
   *  - (set.fold f t (set.union A B)) = (set.fold f (set.fold f t A) B))
   *  where f: T -> S -> S, and t : S
   */
  RewriteResponse postRewriteFold(TNode n);
  /**
   *  rewrites for n include:
   *  - ((_ rel.group n1 ... nk) (as set.empty (Relation T))) =
   *          (rel.singleton (as set.empty (Relation T) ))
   *  - ((_ rel.group n1 ... nk) (set.singleton x)) =
   *          (set.singleton (set.singleton x))
   *  - Evaluation of ((_ rel.group n1 ... nk) A) when A is a constant
   */
  RewriteResponse postRewriteGroup(TNode n);
  /**
   * @param n has the form ((_ rel.aggr n1 ... n_k) f initial A)
   * where initial and A are constants
   * @return the aggregation result.
   */
  RewriteResponse postRewriteAggregate(TNode n);
  /**
   * If A has type (Set T), then rewrite ((rel.project n1 ... nk) A) as
   * (set.map (lambda ((t T)) ((_ tuple.project n1 ... nk) t)) A)
   */
  RewriteResponse postRewriteProject(TNode n);
}; /* class TheorySetsRewriter */

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__THEORY_SETS_REWRITER_H */
