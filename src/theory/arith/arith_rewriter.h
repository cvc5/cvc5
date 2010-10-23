/*********************                                                        */
/*! \file arith_rewriter.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/arith_constants.h"
#include "theory/theory.h"
#include "theory/arith/normal_form.h"

#ifndef __CVC4__THEORY__ARITH__REWRITER_H
#define __CVC4__THEORY__ARITH__REWRITER_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithRewriter{
private:
  ArithConstants* d_constants;

  Node makeSubtractionNode(TNode l, TNode r);
  Node makeUnaryMinusNode(TNode n);

  RewriteResponse preRewriteTerm(TNode t);
  RewriteResponse postRewriteTerm(TNode t);

  RewriteResponse rewriteVariable(TNode t);
  RewriteResponse rewriteConstant(TNode t);
  RewriteResponse rewriteMinus(TNode t, bool pre);
  RewriteResponse rewriteUMinus(TNode t, bool pre);
  RewriteResponse rewriteDivByConstant(TNode t, bool pre);

  RewriteResponse preRewritePlus(TNode t);
  RewriteResponse postRewritePlus(TNode t);

  RewriteResponse preRewriteMult(TNode t);
  RewriteResponse postRewriteMult(TNode t);


  RewriteResponse preRewriteAtom(TNode t);
  RewriteResponse postRewriteAtom(TNode t);
  RewriteResponse postRewriteAtomConstantRHS(TNode t);

public:
  ArithRewriter(ArithConstants* ac) : d_constants(ac) {}

  RewriteResponse preRewrite(TNode n);
  RewriteResponse postRewrite(TNode n);

private:
  bool isAtom(TNode n) const { return isRelationOperator(n.getKind()); }
  bool isTerm(TNode n) const { return !isAtom(n); }
};


}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__REWRITER_H */
