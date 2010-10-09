/*********************                                                        */
/*! \file theory_bool.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "theory/theory.h"
#include "theory/booleans/theory_bool.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {
namespace booleans {

RewriteResponse TheoryBool::preRewrite(TNode n, bool topLevel) {
  if(n.getKind() == kind::IFF) {
    NodeManager* nodeManager = NodeManager::currentNM();
    Node tt = nodeManager->mkConst(true);
    Node ff = nodeManager->mkConst(false);

    // rewrite simple cases of IFF
    if(n[0] == tt) {
      // IFF true x
      return RewriteAgain(n[1]);
    } else if(n[1] == tt) {
      // IFF x true
      return RewriteAgain(n[0]);
    } else if(n[0] == ff) {
      // IFF false x
      return RewriteAgain(n[1].notNode());
    } else if(n[1] == ff) {
      // IFF x false
      return RewriteAgain(n[0].notNode());
    } else if(n[0] == n[1]) {
      // IFF x x
      return RewriteComplete(tt);
    } else if(n[0].getKind() == kind::NOT && n[0][0] == n[1]) {
      // IFF (NOT x) x
      return RewriteComplete(ff);
    } else if(n[1].getKind() == kind::NOT && n[1][0] == n[0]) {
      // IFF x (NOT x)
      return RewriteComplete(ff);
    }
  } else if(n.getKind() == kind::ITE) {
    // non-Boolean-valued ITEs should have been removed in place of
    // a variable
    Assert(n.getType().isBoolean());

    NodeManager* nodeManager = NodeManager::currentNM();

    // rewrite simple cases of ITE
    if(n[0] == nodeManager->mkConst(true)) {
      // ITE true x y
      return RewriteAgain(n[1]);
    } else if(n[0] == nodeManager->mkConst(false)) {
      // ITE false x y
      return RewriteAgain(n[2]);
    } else if(n[1] == n[2]) {
      // ITE c x x
      return RewriteAgain(n[1]);
    }
  }

  return RewriteComplete(n);
}


RewriteResponse TheoryBool::postRewrite(TNode n, bool topLevel) {
  if(n.getKind() == kind::IFF) {
    NodeManager* nodeManager = NodeManager::currentNM();
    Node tt = nodeManager->mkConst(true);
    Node ff = nodeManager->mkConst(false);

    // rewrite simple cases of IFF
    if(n[0] == tt) {
      // IFF true x
      return RewriteComplete(n[1]);
    } else if(n[1] == tt) {
      // IFF x true
      return RewriteComplete(n[0]);
    } else if(n[0] == ff) {
      // IFF false x
      return RewriteAgain(n[1].notNode());
    } else if(n[1] == ff) {
      // IFF x false
      return RewriteAgain(n[0].notNode());
    } else if(n[0] == n[1]) {
      // IFF x x
      return RewriteComplete(tt);
    } else if(n[0].getKind() == kind::NOT && n[0][0] == n[1]) {
      // IFF (NOT x) x
      return RewriteComplete(ff);
    } else if(n[1].getKind() == kind::NOT && n[1][0] == n[0]) {
      // IFF x (NOT x)
      return RewriteComplete(ff);
    }

    if(n[1] < n[0]) {
      // normalize (IFF x y) ==> (IFF y x), if y < x
      return RewriteComplete(n[1].iffNode(n[0]));
    }
  } else if(n.getKind() == kind::ITE) {
    // non-Boolean-valued ITEs should have been removed in place of
    // a variable
    Assert(n.getType().isBoolean());

    NodeManager* nodeManager = NodeManager::currentNM();

    // rewrite simple cases of ITE
    if(n[0] == nodeManager->mkConst(true)) {
      // ITE true x y
      return RewriteComplete(n[1]);
    } else if(n[0] == nodeManager->mkConst(false)) {
      // ITE false x y
      return RewriteComplete(n[2]);
    } else if(n[1] == n[2]) {
      // ITE c x x
      return RewriteComplete(n[1]);
    }

    if(n[0].getKind() == kind::NOT) {
      // rewrite  (ITE (NOT c) x y)  to  (ITE c y x)
      Node out = nodeManager->mkNode(kind::ITE, n[0][0], n[2], n[1]);
      return RewriteComplete(out);
    }
  }

  return RewriteComplete(n);
}

Node TheoryBool::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE:
    // case for Boolean vars is implemented in TheoryEngine (since it
    // appeals to the PropEngine to get the value)
    Unreachable();

  case kind::EQUAL: // 2 args
    // should be handled by IFF
    Unreachable();

  case kind::NOT: // 1 arg
    return nodeManager->mkConst(! engine->getValue(n[0]).getConst<bool>());

  case kind::AND: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(! engine->getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(false);
      }
    }
    return nodeManager->mkConst(true);
  }

  case kind::IFF: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<bool>() ==
                                 engine->getValue(n[1]).getConst<bool>() );

  case kind::IMPLIES: // 2 args
    return nodeManager->mkConst( (! engine->getValue(n[0]).getConst<bool>()) ||
                                 engine->getValue(n[1]).getConst<bool>() );

  case kind::OR: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(engine->getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(true);
      }
    }
    return nodeManager->mkConst(false);
  }

  case kind::XOR: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<bool>() !=
                                 engine->getValue(n[1]).getConst<bool>() );

  case kind::ITE: // 3 args
    // all ITEs should be gone except (bool,bool,bool) ones
    Assert( n[1].getType() == nodeManager->booleanType() &&
            n[2].getType() == nodeManager->booleanType() );
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<bool>() ?
                                 engine->getValue(n[1]).getConst<bool>() :
                                 engine->getValue(n[2]).getConst<bool>() );

  default:
    Unhandled(n.getKind());
  }
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
