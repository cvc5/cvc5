/*********************                                                        */
/*! \file theory_builtin_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
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

#ifndef __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H
#define __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H

#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class TheoryBuiltinRewriter {

  static Node blastDistinct(TNode node);
  static Node blastChain(TNode node);

public:

  static inline RewriteResponse doRewrite(TNode node) {
    switch(node.getKind()) {
    case kind::DISTINCT:
      return RewriteResponse(REWRITE_DONE, blastDistinct(node));
    case kind::CHAIN:
      return RewriteResponse(REWRITE_DONE, blastChain(node));
    default:
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  static inline RewriteResponse postRewrite(TNode node) {
    return doRewrite(node);
  }

  static inline RewriteResponse preRewrite(TNode node) {
    return doRewrite(node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryBuiltinRewriter */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H */
