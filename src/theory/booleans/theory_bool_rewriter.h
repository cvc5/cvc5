/*
 * theory_bool_rewriter.h
 *
 *  Created on: Dec 21, 2010
 *      Author: dejan
 */

#pragma once

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBoolRewriter {

public:

  static RewriteResponse preRewrite(TNode node);
  static RewriteResponse postRewrite(TNode node) {
    return preRewrite(node);
  }

  static void init() {}
  static void shutdown() {}

};

}
}
}
