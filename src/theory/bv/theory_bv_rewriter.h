/*********************                                                        */
/*! \file theory_bv_rewriter.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_REWRITER_H
#define __CVC4__THEORY__BV__THEORY_BV_REWRITER_H

#include "theory/rewriter.h"
#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace bv {

struct AllRewriteRules;
typedef RewriteResponse (*RewriteFunction) (TNode);

class TheoryBVRewriter {
  // static CVC4_THREADLOCAL(AllRewriteRules*) s_allRules;
  // static CVC4_THREADLOCAL(TimerStat*) d_rewriteTimer; 
  static CVC4_THREADLOCAL(RewriteFunction) d_rewriteTable[kind::LAST_KIND];

  static RewriteResponse IdentityRewrite(TNode node);
  static RewriteResponse UndefinedRewrite(TNode node); 

  static void initializeRewrites();
  
  static RewriteResponse RewriteEqual(TNode node);
  static RewriteResponse RewriteUlt(TNode node);
  static RewriteResponse RewriteSlt(TNode node);
  static RewriteResponse RewriteUle(TNode node);
  static RewriteResponse RewriteSle(TNode node);
  static RewriteResponse RewriteUgt(TNode node);
  static RewriteResponse RewriteSgt(TNode node);
  static RewriteResponse RewriteUge(TNode node);
  static RewriteResponse RewriteSge(TNode node);
  static RewriteResponse RewriteNot(TNode node);
  static RewriteResponse RewriteConcat(TNode node);
  static RewriteResponse RewriteAnd(TNode node);
  static RewriteResponse RewriteOr(TNode node);
  static RewriteResponse RewriteXnor(TNode node);
  static RewriteResponse RewriteXor(TNode node);
  static RewriteResponse RewriteNand(TNode node);
  static RewriteResponse RewriteNor(TNode node);
  static RewriteResponse RewriteComp(TNode node);
  static RewriteResponse RewriteMult(TNode node);
  static RewriteResponse RewritePlus(TNode node);
  static RewriteResponse RewriteSub(TNode node);
  static RewriteResponse RewriteNeg(TNode node);
  static RewriteResponse RewriteUdiv(TNode node);
  static RewriteResponse RewriteUrem(TNode node);
  static RewriteResponse RewriteSmod(TNode node);
  static RewriteResponse RewriteSdiv(TNode node);
  static RewriteResponse RewriteSrem(TNode node);
  static RewriteResponse RewriteShl(TNode node);
  static RewriteResponse RewriteLshr(TNode node);
  static RewriteResponse RewriteAshr(TNode node);
  static RewriteResponse RewriteExtract(TNode node);
  static RewriteResponse RewriteRepeat(TNode node);
  static RewriteResponse RewriteZeroExtend(TNode node);
  static RewriteResponse RewriteSignExtend(TNode node);
  static RewriteResponse RewriteRotateRight(TNode node);
  static RewriteResponse RewriteRotateLeft(TNode node);

public:

  static RewriteResponse postRewrite(TNode node);

  static RewriteResponse preRewrite(TNode node);

  static inline Node rewriteEquality(TNode node) {
    Debug("bitvector") << "TheoryBV::rewriteEquality(" << node << ")" << std::endl;
    return postRewrite(node).node;
  }

  static void init();
  static void shutdown();
  
};/* class TheoryBVRewriter */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_REWRITER_H */
