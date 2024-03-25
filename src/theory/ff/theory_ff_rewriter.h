/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * FiniteFields theory rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__THEORY_FF_REWRITER_H
#define CVC5__THEORY__FF__THEORY_FF_REWRITER_H

#include <optional>
#include <utility>

#include "expr/node.h"
#include "theory/rewriter.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class TheoryFiniteFieldsRewriter : public TheoryRewriter
{
 public:
  TheoryFiniteFieldsRewriter(NodeManager* nm);
  /**
   * Rewrite a node into the normal form for the theory of ff.
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
   *
   * Ensures:
   *  - addition and multiplication results are flat
   *  - addition and multiplication terms have at most one constant, in the
   *    final position
   *  - addition terms do not have the 0 constant
   *  - multiplication terms do not have a 0 or 1 constant
   *
   */
  RewriteResponse postRewrite(TNode node) override;

  /**
   * Rewrite a node into the normal form for the theory of ff
   * in pre-order (really topological order)---meaning that the
   * children may not be in the normal form.  This is an optimization
   * for theories with cancelling terms (e.g., 0 * (big-nasty-expression)
   * in arithmetic rewrites to 0 without the need to look at the big
   * nasty expression).  Since it's only an optimization, the
   * implementation here can do nothing.
   */
  RewriteResponse preRewrite(TNode node) override;

 private:
  /** Make n-ary node */
  Node mkNary(Kind k, std::vector<Node>&& children);
  /** Parse as a product with a constant scalar
   *
   *  If there is no constant scalar, returns a 1.
   */
  std::pair<Node, FiniteFieldValue> parseScalar(TNode t);
  /** preRewrite negation */
  Node preRewriteFfNeg(TNode t);
  /** preRewrite addition */
  Node preRewriteFfAdd(TNode t);
  /** postRewrite addition */
  Node postRewriteFfAdd(TNode t);
  /** preRewrite multiplication */
  Node preRewriteFfMult(TNode t);
  /** postRewrite multiplication */
  Node postRewriteFfMult(TNode t);
  /** postRewrite equality */
  Node postRewriteFfEq(TNode t);
}; /* class TheoryFiniteFieldsRewriter */

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__THEORY_FF_REWRITER_H */
