/*
 * theory_builtin_rewriter.h
 *
 *  Created on: Dec 21, 2010
 *      Author: dejan
 */

#pragma once

#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class TheoryBuiltinRewriter {

  static Node blastDistinct(TNode node);

public:

  static inline RewriteResponse postRewrite(TNode node) {
    if (node.getKind() == kind::EQUAL) {
      return Rewriter::callPostRewrite(Theory::theoryOf(node[0]), node);
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline RewriteResponse preRewrite(TNode node) {
    switch(node.getKind()) {
    case kind::DISTINCT:
      return RewriteResponse(REWRITE_DONE, blastDistinct(node));
    case kind::EQUAL:
      return Rewriter::callPreRewrite(Theory::theoryOf(node[0]), node);
    default:
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  static inline void init() {}
  static inline void shutdown() {}

};

}
}
}
