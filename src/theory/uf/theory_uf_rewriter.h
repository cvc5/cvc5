/*
 * theory_uf_rewriter.h
 *
 *  Created on: Dec 21, 2010
 *      Author: dejan
 */

#pragma once

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUfRewriter {

public:

  static RewriteResponse postRewrite(TNode node) {
    if(node.getKind() == kind::EQUAL || node.getKind() == kind::IFF) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        // If we've switched theories, we need to rewrite again (TODO: THIS IS HACK, once theories accept eq, change)
        if (Theory::theoryOf(newNode[0]) != Theory::theoryOf(newNode[1])) {
          return RewriteResponse(REWRITE_AGAIN_FULL, newNode);
        } else {
          return RewriteResponse(REWRITE_DONE, newNode);
        }
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static RewriteResponse preRewrite(TNode node) {
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};

}
}
}
