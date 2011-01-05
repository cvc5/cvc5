/*
 * rewriter_attributes.h
 *
 *  Created on: Dec 27, 2010
 *      Author: dejan
 */

#pragma once

namespace CVC4 {
namespace theory {

template <bool pre, theory::TheoryId theoryId>
struct RewriteCacheTag {};

template <theory::TheoryId theoryId>
struct RewriteAttibute {

  typedef expr::Attribute< RewriteCacheTag<true, theoryId>, Node> pre_rewrite;
  typedef expr::Attribute< RewriteCacheTag<false, theoryId>, Node> post_rewrite;

  /**
   * Get the value of the pre-rewrite cache.
   */
  static Node getPreRewriteCache(TNode node) throw() {
    Node cache;
    if (node.hasAttribute(pre_rewrite())) {
      node.getAttribute(pre_rewrite(), cache);
    } else {
      return Node::null();
    }
    if (cache.isNull()) {
      return node;
    } else {
      return cache;
    }
  }

  /**
   * Set the value of the pre-rewrite cache.
   */
  static void setPreRewriteCache(TNode node, TNode cache) throw() {
    Debug("rewriter") << "setting pre-rewrite of " << node << " to " << cache << std::endl;
    Assert(!cache.isNull());
    if (node == cache) {
      node.setAttribute(pre_rewrite(), Node::null());
    } else {
      node.setAttribute(pre_rewrite(), cache);
    }
  }

  /**
   * Get the value of the post-rewrite cache.
   * none).
   */
  static Node getPostRewriteCache(TNode node) throw() {
    Node cache;
    if (node.hasAttribute(post_rewrite())) {
      node.getAttribute(post_rewrite(), cache);
    } else {
      return Node::null();
    }
    if (cache.isNull()) {
      return node;
    } else {
      return cache;
    }
  }

  /**
   * Set the value of the post-rewrite cache.  v cannot be a null Node.
   */
  static void setPostRewriteCache(TNode node, TNode cache) throw() {
    Assert(!cache.isNull());
    Debug("rewriter") << "setting rewrite of " << node << " to " << cache << std::endl;
    if (node == cache) {
      node.setAttribute(post_rewrite(), Node::null());
    } else {
      node.setAttribute(post_rewrite(), cache);
    }
  }
};

} // Namespace CVC4
} // Namespace theory

