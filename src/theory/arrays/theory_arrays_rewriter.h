/*********************                                                        */
/*! \file theory_arrays_rewriter.h
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

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArraysRewriter {

public:

  static RewriteResponse postRewrite(TNode node) {
    Debug("arrays-postrewrite") << "Arrays::postRewrite start " << node << std::endl;
    if(node.getKind() == kind::EQUAL || node.getKind() == kind::IFF) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      // checks for RoW axiom: (select ( store a i v) i) = v and rewrites it
      // to true
      if(node[0].getKind()==kind::SELECT) {
        TNode a = node[0][0];
        TNode j = node[0][1];
        if(a.getKind()==kind::STORE) {
          TNode b = a[0];
          TNode i = a[1];
          TNode v = a[2];
          if(v == node[1] && i == j) {
            Debug("arrays-postrewrite") << "Arrays::postRewrite true" << std::endl;
            return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
          }
        }
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
    // FIXME: would it be better to move in preRewrite?
    // if yes don't need the above case
    if (node.getKind()==kind::SELECT) {
      // we are rewriting (select (store a i v) i) to v
      TNode a = node[0];
      TNode i = node[1];
      if(a.getKind() == kind::STORE) {
        TNode b = a[0];
        TNode j = a[1];
        TNode v = a[2];
        if(i==j) {
          Debug("arrays-postrewrite") << "Arrays::postrewrite to " << v << std::endl;
          return RewriteResponse(REWRITE_AGAIN_FULL, v);
        }
      }
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline RewriteResponse preRewrite(TNode node) {
    Debug("arrays-prerewrite") << "Arrays::preRewrite " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryArraysRewriter */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
