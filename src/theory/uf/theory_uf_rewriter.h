/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__THEORY_UF_REWRITER_H
#define CVC5__THEORY__UF__THEORY_UF_REWRITER_H

#include "expr/node_algorithm.h"
#include "options/uf_options.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

class TheoryUfRewriter : public TheoryRewriter
{
 public:
  TheoryUfRewriter();
  /** post-rewrite */
  RewriteResponse postRewrite(TNode node) override;
  /** pre-rewrite */
  RewriteResponse preRewrite(TNode node) override;
  // conversion between HO_APPLY AND APPLY_UF
  /**
   * converts an APPLY_UF to a curried HO_APPLY e.g.
   * (f a b) becomes (@ (@ f a) b).
   */
  static Node getHoApplyForApplyUf(TNode n);
  /**
   * Converts a curried HO_APPLY into an APPLY_UF e.g.
   * (@ (@ f a) b) becomes (f a b).
   * Returns null if f cannot be used as an operator for APPLY_UF (see
   * canUseAsApplyUfOperator).
   */
  static Node getApplyUfForHoApply(TNode n);
  /**
   * Given a curried HO_APPLY term n, this method adds its arguments into args
   * and returns its operator. If the argument opInArgs is true, then we add
   * its operator to args.
   */
  static Node decomposeHoApply(TNode n,
                               std::vector<TNode>& args,
                               bool opInArgs = false);
  /** returns true if this node can be used as an operator of an APPLY_UF node.  In higher-order logic,
   * terms can have function types and not just variables. 
   * Currently, we want only free variables to be used as operators of APPLY_UF nodes. This is motivated by
   * E-matching, ite-lifting among other things.  For example:
   * f: Int -> Int, g : Int -> Int
   * forall x : ( Int -> Int ), y : Int. (x y) = (f 0)
   * Then, f and g can be used as APPLY_UF operators, but (ite C f g), (lambda x1. (f x1)) as well as the variable x above are not.
   */
  static bool canUseAsApplyUfOperator(TNode n);

 private:
  /** Entry point for rewriting lambdas */
  static Node rewriteLambda(Node node);
  /** rewrite bv2nat */
  static RewriteResponse rewriteBVToNat(TNode node);
  /** rewrite int2bv */
  static RewriteResponse rewriteIntToBV(TNode node);
}; /* class TheoryUfRewriter */

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__THEORY_UF_REWRITER_H */
