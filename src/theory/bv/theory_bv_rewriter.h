/*********************                                                        */
/*! \file theory_bv_rewriter.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
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

namespace CVC4 {
namespace theory {
namespace bv {

class AllRewriteRules;

class TheoryBVRewriter {

  static AllRewriteRules* s_allRules;

public:

  static RewriteResponse postRewrite(TNode node);

  static inline RewriteResponse preRewrite(TNode node) {
    return RewriteResponse(REWRITE_DONE, node);
  }

  static void init();
  static void shutdown();
};/* class TheoryBVRewriter */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_REWRITER_H */
