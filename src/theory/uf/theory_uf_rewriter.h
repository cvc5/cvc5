/*********************                                                        */
/*! \file theory_uf_rewriter.h
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

#ifndef __CVC4__THEORY__UF__THEORY_UF_REWRITER_H
#define __CVC4__THEORY__UF__THEORY_UF_REWRITER_H

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
    if(node.getKind() == kind::EQUAL || node.getKind() == kind::IFF) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryUfRewriter */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_REWRITER_H */
