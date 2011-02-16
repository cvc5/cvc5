/*
 * theory_bv_rewriter.h
 *
 *  Created on: Dec 21, 2010
 *      Author: dejan
 */

#pragma once

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
};

}
}
}
