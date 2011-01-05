#include <algorithm>
#include "theory/booleans/theory_bool_rewriter.h"

namespace CVC4 {
namespace theory {
namespace booleans {

RewriteResponse TheoryBoolRewriter::preRewrite(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();
  Node tt = nodeManager->mkConst(true);
  Node ff = nodeManager->mkConst(false);

  switch(n.getKind()) {
  case kind::NOT: {
    if (n[0] == tt) return RewriteResponse(REWRITE_DONE, ff);
    if (n[0] == ff) return RewriteResponse(REWRITE_DONE, tt);
    if (n[0].getKind() == kind::NOT) return RewriteResponse(REWRITE_AGAIN, n[0][0]);
    break;
  }
  case kind::IFF: {
    // rewrite simple cases of IFF
    if(n[0] == tt) {
      // IFF true x
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    } else if(n[1] == tt) {
      // IFF x true
      return RewriteResponse(REWRITE_AGAIN, n[0]);
    } else if(n[0] == ff) {
      // IFF false x
      return RewriteResponse(REWRITE_AGAIN, n[1].notNode());
    } else if(n[1] == ff) {
      // IFF x false
      return RewriteResponse(REWRITE_AGAIN, n[0].notNode());
    } else if(n[0] == n[1]) {
      // IFF x x
      return RewriteResponse(REWRITE_DONE, tt);
    } else if(n[0].getKind() == kind::NOT && n[0][0] == n[1]) {
      // IFF (NOT x) x
      return RewriteResponse(REWRITE_DONE, ff);
    } else if(n[1].getKind() == kind::NOT && n[1][0] == n[0]) {
      // IFF x (NOT x)
      return RewriteResponse(REWRITE_DONE, ff);
    }
    break;
  }
  case kind::ITE: {
    // non-Boolean-valued ITEs should have been removed in place of
    // a variable
    Assert(n.getType().isBoolean());
    // rewrite simple cases of ITE
    if(n[0] == tt) {
      // ITE true x y
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    } else if(n[0] == ff) {
      // ITE false x y
      return RewriteResponse(REWRITE_AGAIN, n[2]);
    } else if(n[1] == n[2]) {
      // ITE c x x
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    }
    break;
  }
  default:
    return RewriteResponse(REWRITE_DONE, n);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

}
}
}

