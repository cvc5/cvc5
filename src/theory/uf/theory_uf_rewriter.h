/*********************                                                        */
/*! \file theory_uf_rewriter.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
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
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    }
    if(node.getKind() == kind::APPLY_UF && node.getOperator().getKind() == kind::LAMBDA) {
      // resolve away the lambda
      context::Context fakeContext;
      theory::SubstitutionMap substitutions(&fakeContext);
      TNode lambda = node.getOperator();
      for(TNode::iterator formal = lambda[0].begin(), arg = node.begin(); formal != lambda[0].end(); ++formal, ++arg) {
        // typechecking should ensure that the APPLY_UF is well-typed, correct arity, etc.
        Assert(formal != node.end());
        substitutions.addSubstitution(*formal, *arg);
      }
      return RewriteResponse(REWRITE_DONE, substitutions.apply(lambda[1]));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static RewriteResponse preRewrite(TNode node) {
    if(node.getKind() == kind::EQUAL || node.getKind() == kind::IFF) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
    }
    if(node.getKind() == kind::APPLY_UF && node.getOperator().getKind() == kind::LAMBDA) {
      // resolve away the lambda
      context::Context fakeContext;
      theory::SubstitutionMap substitutions(&fakeContext);
      TNode lambda = node.getOperator();
      for(TNode::iterator formal = lambda[0].begin(), arg = node.begin(); formal != lambda[0].end(); ++formal, ++arg) {
        // typechecking should ensure that the APPLY_UF is well-typed, correct arity, etc.
        Assert(formal != node.end());
        substitutions.addSubstitution(*formal, *arg);
      }
      return RewriteResponse(REWRITE_DONE, substitutions.apply(lambda[1]));
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
