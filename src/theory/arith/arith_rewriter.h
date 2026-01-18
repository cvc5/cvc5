/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  ArithRewriter(NodeManager* nm, OperatorElim& oe, bool expertEnabled = true);
  RewriteResponse preRewrite(TNode n) override;
  RewriteResponse postRewrite(TNode n) override;
  /**
   * Expand definition, which eliminates extended operators like div/mod in
   * the given node.
   */
  Node expandDefinition(Node node) override;
  /**
   * Rewrite inequality to bv. If ineq contains a single bv2nat term, then
   * if possible, return an equivalent formula involving a bitvector inequality.
   * Otherwise, return ineq itself.
   */
  Node rewriteIneqToBv(const Node& ineq);

  /**
   * Rewrite n based on the proof rewrite rule id.
   * @param id The rewrite rule.
   * @param n The node to rewrite.
   * @return The rewritten version of n based on id, or Node::null() if n
   * cannot be rewritten.
   */
  Node rewriteViaRule(ProofRewriteRule id, const Node& n) override;

 private:
  /** preRewrite for atoms */
  RewriteResponse preRewriteAtom(TNode t);
  /** postRewrite for atoms */
  RewriteResponse postRewriteAtom(TNode t);

  /** preRewrite for terms */
  RewriteResponse preRewriteTerm(TNode t);
  /** postRewrite for terms */
  RewriteResponse postRewriteTerm(TNode t);

  /** Post-rewrites that are only available in expert mode */
  RewriteResponse postRewriteExpert(TNode t);

  /** rewrite real algebraic numbers */
  RewriteResponse rewriteRAN(TNode t);
  /** rewrite variables */
  RewriteResponse rewriteVariable(TNode t);

  /** rewrite unary minus */
  RewriteResponse rewriteNeg(TNode t, bool pre);
  /** rewrite binary minus */
  RewriteResponse rewriteSub(TNode t);
  /** preRewrite addition */
  RewriteResponse preRewritePlus(TNode t);
  /** postRewrite addition */
  RewriteResponse postRewritePlus(TNode t);
  /** preRewrite multiplication */
  RewriteResponse preRewriteMult(TNode t);
  /** postRewrite multiplication */
  RewriteResponse postRewriteMult(TNode t);

  /** rewrite division */
  RewriteResponse rewriteDiv(TNode t, bool pre);
  /** rewrite to_real */
  RewriteResponse rewriteToReal(TNode t);
  /** rewrite absolute */
  RewriteResponse rewriteAbs(TNode t);
  /** rewrite integer division and modulus */
  RewriteResponse rewriteIntsDivMod(TNode t, bool pre);
  /** rewrite integer total division and total modulus */
  RewriteResponse rewriteIntsDivModTotal(TNode t, bool pre);
  /** rewrite to_int and is_int */
  RewriteResponse rewriteExtIntegerOp(TNode t);

  /** postRewrite IAND */
  RewriteResponse postRewriteIAnd(TNode t);
  /** postRewrite PIAND */
  RewriteResponse postRewritePIAnd(TNode t);
  /** postRewrite POW2 */
  RewriteResponse postRewritePow2(TNode t);
  /** postRewrite INTS_IS_POW2 */
  RewriteResponse postRewriteIntsIsPow2(TNode t);
  /** postRewrite INTS_LOG2 */
  RewriteResponse postRewriteIntsLog2(TNode t);

  /** postRewrite transcendental functions */
  RewriteResponse postRewriteTranscendental(TNode t);

  /** return rewrite */
  RewriteResponse returnRewrite(TNode t, Node ret, Rewrite r);
  /**
   * Return the result of expanding (^ x c) for constant c.
   */
  static Node expandPowConst(NodeManager* nm, const Node& n);
  /**
   * Rewrite inequality to bv. If applicable, return
   * the bitvector inequality that is the rewritten form of the arithmetic
   * inequality ineq that is equivalent to (<k> sum 0).
   */
  Node rewriteIneqToBv(Kind k, const rewriter::Sum& sum, const Node& ineq);
  /** The operator elimination utility */
  OperatorElim& d_opElim;
  /** Whether we permit reasoning about expert extensions of arithmetic */
  bool d_expertEnabled;
}; /* class ArithRewriter */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_REWRITER_H */
