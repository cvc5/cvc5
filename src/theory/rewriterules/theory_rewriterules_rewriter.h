/*********************                                                        */
/*! \file theory_rewriterules_rewriter.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_REWRITER_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_REWRITER_H

#include "theory/rewriter.h"
#include "theory/rewriter_attributes.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {

class TheoryRewriterulesRewriter {
public:

  /**
   * Rewrite a node into the normal form for the theory of rewriterules.
   * Called in post-order (really reverse-topological order) when
   * traversing the expression DAG during rewriting.  This is the
   * main function of the rewriter, and because of the ordering,
   * it can assume its children are all rewritten already.
   *
   * This function can return one of three rewrite response codes
   * along with the rewritten node:
   *
   *   REWRITE_DONE indicates that no more rewriting is needed.
   *   REWRITE_AGAIN means that the top-level expression should be
   *     rewritten again, but that its children are in final form.
   *   REWRITE_AGAIN_FULL means that the entire returned expression
   *     should be rewritten again (top-down with preRewrite(), then
   *     bottom-up with postRewrite()).
   *
   * Even if this function returns REWRITE_DONE, if the returned
   * expression belongs to a different theory, it will be fully
   * rewritten by that theory's rewriter.
   */
  static RewriteResponse postRewrite(TNode node) {

    // Implement me!

    // This default implementation
    return RewriteResponse(REWRITE_DONE, node);
  }

  /**
   * Rewrite a node into the normal form for the theory of rewriterules
   * in pre-order (really topological order)---meaning that the
   * children may not be in the normal form.  This is an optimization
   * for theories with cancelling terms (e.g., 0 * (big-nasty-expression)
   * in arithmetic rewrites to 0 without the need to look at the big
   * nasty expression).  Since it's only an optimization, the
   * implementation here can do nothing.
   */
  static RewriteResponse preRewrite(TNode node) {
    // do nothing
    return RewriteResponse(REWRITE_DONE, node);
  }

  /**
   * Initialize the rewriter.
   */
  static inline void init() {
    // nothing to do
  }

  /**
   * Shut down the rewriter.
   */
  static inline void shutdown() {
    // nothing to do
  }

};/* class TheoryRewriterulesRewriter */

}/* CVC4::theory::rewriterules namespace */

template<>
struct RewriteAttibute<THEORY_REWRITERULES> {
  static Node getPreRewriteCache(TNode node) throw() {
    return node;
  }

  static void setPreRewriteCache(TNode node, TNode cache) throw() { }

  static Node getPostRewriteCache(TNode node) throw() {
    return node;
  }

  static void setPostRewriteCache(TNode node, TNode cache) throw() { }

  typedef expr::Attribute< RewriteCacheTag<true, THEORY_REWRITERULES>, Node> pre_rewrite;
  typedef expr::Attribute< RewriteCacheTag<false, THEORY_REWRITERULES>, Node> post_rewrite;
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_REWRITER_H */
