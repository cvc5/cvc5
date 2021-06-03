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
  static Node makeSubtractionNode(TNode l, TNode r);
  static Node makeUnaryMinusNode(TNode n);

  static RewriteResponse preRewriteTerm(TNode t);
  static RewriteResponse postRewriteTerm(TNode t);

  static RewriteResponse rewriteVariable(TNode t);
  static RewriteResponse rewriteConstant(TNode t);
  static RewriteResponse rewriteMinus(TNode t, bool pre);
  static RewriteResponse rewriteUMinus(TNode t, bool pre);
  static RewriteResponse rewriteDiv(TNode t, bool pre);
  static RewriteResponse rewriteIntsDivMod(TNode t, bool pre);
  static RewriteResponse rewriteIntsDivModTotal(TNode t, bool pre);

  static RewriteResponse preRewritePlus(TNode t);
  static RewriteResponse postRewritePlus(TNode t);

  static RewriteResponse preRewriteMult(TNode t);
  static RewriteResponse postRewriteMult(TNode t);

  static RewriteResponse postRewriteIAnd(TNode t);

  static RewriteResponse preRewriteTranscendental(TNode t);
  static RewriteResponse postRewriteTranscendental(TNode t);

  static RewriteResponse preRewriteAtom(TNode t);
  static RewriteResponse postRewriteAtom(TNode t);

  static bool isAtom(TNode n);

  static inline bool isTerm(TNode n) {
    return !isAtom(n);
  }
  /** return rewrite */
  static RewriteResponse returnRewrite(TNode t, Node ret, Rewrite r);
  /** The operator elimination utility */
  OperatorElim& d_opElim;
}; /* class ArithRewriter */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__ARITH_REWRITER_H */
