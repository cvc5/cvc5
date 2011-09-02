/*********************                                                        */
/*! \file theory_arrays_rewriter.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: barrett, mdeters
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

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArraysRewriter {

public:

  static RewriteResponse postRewrite(TNode node) {
    Trace("arrays-postrewrite") << "Arrays::postRewrite start " << node << std::endl;
    switch (node.getKind()) {
      case kind::SELECT: {
        // select(store(a,i,v),i) = v
        TNode store = node[0];
        if (store.getKind() == kind::STORE &&
            store[1] == node[1]) {
          return RewriteResponse(REWRITE_DONE, store[2]);
        }
        break;
      }
      case kind::STORE: {
        TNode store = node[0];
        TNode value = node[2];
        // store(a,i,select(a,i)) = a
        if (value.getKind() == kind::SELECT &&
            value[0] == store &&
            value[1] == node[1]) {
          return RewriteResponse(REWRITE_DONE, store);
        }
        // store(store(a,i,v),i,w) = store(a,i,w)
        if (store.getKind() == kind::STORE &&
            store[1] == node[1]) {
          Node newNode = NodeManager::currentNM()->mkNode(kind::STORE, store[0], store[1], value);
          return RewriteResponse(REWRITE_AGAIN_FULL, newNode);
        }
        break;
      }
      case kind::EQUAL:
      case kind::IFF: {
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
        break;
      }
      default:
        break;
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline RewriteResponse preRewrite(TNode node) {
    Trace("arrays-prerewrite") << "Arrays::preRewrite " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryArraysRewriter */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
