/*********************                                                        */
/*! \file arith_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for arithmetic.
 **
 ** Rewriter for the theory of arithmetic.  This rewrites to the normal form for
 ** arithmetic. See theory/arith/normal_form.h for more information.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_REWRITER_H
#define CVC4__THEORY__ARITH__ARITH_REWRITER_H

#include "theory/theory.h"
#include "theory/theory_rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithRewriter : public TheoryRewriter
{
 public:
  RewriteResponse preRewrite(TNode n) override;
  RewriteResponse postRewrite(TNode n) override;

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
  static RewriteResponse rewriteIntsDivModTotal(TNode t, bool pre);

  static RewriteResponse preRewritePlus(TNode t);
  static RewriteResponse postRewritePlus(TNode t);

  static RewriteResponse preRewriteMult(TNode t);
  static RewriteResponse postRewriteMult(TNode t);
  
  static RewriteResponse preRewriteTranscendental(TNode t);
  static RewriteResponse postRewriteTranscendental(TNode t);

  static RewriteResponse preRewriteAtom(TNode t);
  static RewriteResponse postRewriteAtom(TNode t);

  static bool isAtom(TNode n);

  static inline bool isTerm(TNode n) {
    return !isAtom(n);
  }

}; /* class ArithRewriter */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__ARITH_REWRITER_H */
