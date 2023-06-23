/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter for the theory of arithmetic.
 *
 * This rewrites to the normal form for arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_REWRITER_H
#define CVC5__THEORY__ARITH__ARITH_REWRITER_H

#include "theory/arith/rewriter/addition.h"
#include "theory/arith/rewrites.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {
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
  /**
   * Rewrite inequality to bv. If ineq contains a single bv2nat term, then
   * if possible, return an equivalent formula involving a bitvector inequality.
   * Otherwise, return ineq itself.
   */
  static Node rewriteIneqToBv(const Node& ineq);

 private:
  /** preRewrite for atoms */
  static RewriteResponse preRewriteAtom(TNode t);
  /** postRewrite for atoms */
  static RewriteResponse postRewriteAtom(TNode t);

  /** preRewrite for terms */
  static RewriteResponse preRewriteTerm(TNode t);
  /** postRewrite for terms */
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
  /** preRewrite multiplication */
  static RewriteResponse preRewriteMult(TNode t);
  /** postRewrite multiplication */
  static RewriteResponse postRewriteMult(TNode t);

  /** rewrite division */
  static RewriteResponse rewriteDiv(TNode t, bool pre);
  /** rewrite to_real */
  static RewriteResponse rewriteToReal(TNode t);
  /** rewrite absolute */
  static RewriteResponse rewriteAbs(TNode t);
  /** rewrite integer division and modulus */
  static RewriteResponse rewriteIntsDivMod(TNode t, bool pre);
  /** rewrite integer total division and total modulus */
  static RewriteResponse rewriteIntsDivModTotal(TNode t, bool pre);
  /** rewrite to_int and is_int */
  static RewriteResponse rewriteExtIntegerOp(TNode t);

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

  /**
   * Rewrite inequality to bv. If applicable, return
   * the bitvector inequality that is the rewritten form of the arithmetic
   * inequality ineq that is equivalent to (<k> sum 0).
   */
  static Node rewriteIneqToBv(Kind k,
                              const rewriter::Sum& sum,
                              const Node& ineq);
  /** The operator elimination utility */
  OperatorElim& d_opElim;
}; /* class ArithRewriter */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_REWRITER_H */
