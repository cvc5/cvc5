/*********************                                                        */
/*! \file theory_fp_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_REWRITER_H
#define __CVC4__THEORY__FP__THEORY_FP_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace fp {

typedef RewriteResponse (*RewriteFunction) (TNode, bool);

class TheoryFpRewriter {
 protected :
  static RewriteFunction preRewriteTable[kind::LAST_KIND];
  static RewriteFunction postRewriteTable[kind::LAST_KIND];

 public:

  static RewriteResponse preRewrite(TNode node);
  static RewriteResponse postRewrite(TNode node);


  /**
   * Rewrite an equality, in case special handling is required.
   */
  static Node rewriteEquality(TNode equality) {
    // often this will suffice
    return postRewrite(equality).node;
  }

  static void init();

  /**
   * Shut down the rewriter.
   */
  static inline void shutdown() {
    // nothing to do
  }

};/* class TheoryFpRewriter */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_REWRITER_H */
