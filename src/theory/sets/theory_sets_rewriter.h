/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Kshitij Bansal, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  TheorySetsRewriter(NodeManager* nm);

  /**
   * Rewrite n based on the proof rewrite rule id.
   * @param id The rewrite rule.
   * @param n The node to rewrite.
   * @return The rewritten version of n based on id, or Node::null() if n
   * cannot be rewritten.
   */
  Node rewriteViaRule(ProofRewriteRule id, const Node& n) override;

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

  /**
   * Rewrite membership for a binary op.
   * For example, if mem is (set.member x (set.inter A B)), the returns the
   * formula (and (set.member x A) (set.member x B)).
   * @param mem The membership.
   * @return The rewritten form of the membership.
   */
  Node rewriteMembershipBinaryOp(const Node& mem);

 private:
  /**
   * Returns true if elementTerm is in setTerm, where both terms are constants.
   */
  bool checkConstantMembership(TNode elementTerm, TNode setTerm);
  /**
   * Rewrite set comprehension
   */
  RewriteResponse postRewriteComprehension(TNode n);
  RewriteResponse postRewriteTableJoin(TNode n);
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
   *  - (set.all p (as set.empty (Set T)) is rewritten as true
   *  - (set.all p (set.singleton x)) is rewritten as (p x)
   *  - (set.all p (set.union A B)) is rewritten as
   *       (and (set.all p A) (set.all p B))
   *  - otherwise (set.all p A) is rewritten as (= (set.filter p A) A)
   *  where p: T -> Bool
   */
  RewriteResponse postRewriteAll(TNode n);
  /**
   *  rewrites for n include:
   *  - (set.some p (as set.empty (Set T)) is rewritten as false
   *  - (set.some p (set.singleton x)) is rewritten as  (p x)
   *  - (set.some p (set.union A B)) is rewritten as
   *       (or (set.some p A) (set.some p B))
   *  - otherwise (set.some p A) is rewritten as
   *       (distinct (set.filter p A) (as set.empty (Set T)))
   *  where p: T -> Bool
   */
  RewriteResponse postRewriteSome(TNode n);
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
