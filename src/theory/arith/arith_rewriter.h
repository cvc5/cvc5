/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter for the theory of arithmetic.
 *
 * This rewrites to the normal form for arithmetic.
 * See theory/arith/normal_form.h for more information.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_REWRITER_H
#define CVC5__THEORY__ARITH__ARITH_REWRITER_H

#include "theory/arith/rewrites.h"
#include "theory/theory_rewriter.h"

namespace cvc5 {
namespace theory {
namespace arith {

class OperatorElim;

class ArithRewriter : public TheoryRewriter
{
 public:
  ArithRewriter(OperatorElim& oe);
  RewriteResponse preRewrite(TNode n) override;
  RewriteResponse postRewrite(TNode n) override;
  /**
   * Expand definition, which eliminates extended operators like div/mod in
   * the given node.
   */
  TrustNode expandDefinition(Node node) override;

 private:
  /** preRewrite for atoms */
  static RewriteResponse preRewriteAtom(TNode t);
  /** postRewrite for atoms */
  static RewriteResponse postRewriteAtom(TNode t);

  static RewriteResponse preRewriteTerm(TNode t);
  static RewriteResponse postRewriteTerm(TNode t);

  /** rewrite real algebraic numbers */
  static RewriteResponse rewriteRAN(TNode t);
  /** rewrite variables */
  static RewriteResponse rewriteVariable(TNode t);

  /** rewrite unary minus */
  static RewriteResponse rewriteNeg(TNode t, bool pre);
  /** rewrite binary minus */
  static RewriteResponse rewriteSub(TNode t);
  /** preRewrite addition */
  static RewriteResponse preRewritePlus(TNode t);
  /** postRewrite addition */
  static RewriteResponse postRewritePlus(TNode t);
  static RewriteResponse rewriteDiv(TNode t, bool pre);
  static RewriteResponse rewriteAbs(TNode t);
  static RewriteResponse rewriteIntsDivMod(TNode t, bool pre);
  static RewriteResponse rewriteIntsDivModTotal(TNode t, bool pre);
  /** Entry for applications of to_int and is_int */
  static RewriteResponse rewriteExtIntegerOp(TNode t);

  static RewriteResponse preRewriteMult(TNode t);
  static RewriteResponse postRewriteMult(TNode t);

  /** postRewrite IAND */
  static RewriteResponse postRewriteIAnd(TNode t);
  /** postRewrite POW2 */
  static RewriteResponse postRewritePow2(TNode t);

  /** preRewrite transcendental functions */
  static RewriteResponse preRewriteTranscendental(TNode t);
  /** postRewrite transcendental functions */
  static RewriteResponse postRewriteTranscendental(TNode t);

  /** return rewrite */
  static RewriteResponse returnRewrite(TNode t, Node ret, Rewrite r);
  /** The operator elimination utility */
  OperatorElim& d_opElim;
}; /* class ArithRewriter */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__ARITH_REWRITER_H */
