#include "cvc4_private.h"

#ifndef __CVC4__THEORY__$id__THEORY_$id_REWRITER_H
#define __CVC4__THEORY__$id__THEORY_$id_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace $dir {

class Theory$camelRewriter {
public:

  /**
   * Rewrite a node into the normal form for the theory of $dir.
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
   * Rewrite a node into the normal form for the theory of $dir
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
   * Rewrite an equality, in case special handling is required.
   */
  static Node rewriteEquality(TNode equality) {
    // often this will suffice
    return postRewrite(equality).node;
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

};/* class Theory$camelRewriter */

}/* CVC4::theory::$dir namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__$id__THEORY_$id_REWRITER_H */
