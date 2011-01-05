/*
 * rewriter.h
 *
 *  Created on: Dec 13, 2010
 *      Author: dejan
 */

#pragma once

#include "expr/node.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {

enum RewriteStatus {
  REWRITE_DONE,
  REWRITE_AGAIN,
  REWRITE_AGAIN_FULL
};

/**
 * Instances of this class serve as response codes from
 * Theory::preRewrite() and Theory::postRewrite().  Instances of
 * derived classes RewriteComplete(n), RewriteAgain(n), and
 * FullRewriteNeeded(n) should be used, giving self-documenting
 * rewrite behavior.
 */
struct RewriteResponse {
  const RewriteStatus status;
  const Node node;
  RewriteResponse(RewriteStatus status, Node node) : status(status), node(node) {}
};

class Rewriter {

  /** Returns the appropriate cache for a node */
  static Node getPreRewriteCache(theory::TheoryId theoryId, TNode node);

  /** Returns the appropriate cache for a node */
  static Node getPostRewriteCache(theory::TheoryId theoryId, TNode node);

  /** Sets the appropriate cache for a node */
  static void setPreRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache);

  /** Sets the appropriate cache for a node */
  static void setPostRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache);

public:

  /** Calls the pre rewrite for the given theory */
  static RewriteResponse callPreRewrite(theory::TheoryId theoryId, TNode node);

  /** Calls the post rewrite for the given theory */
  static RewriteResponse callPostRewrite(theory::TheoryId theoryId, TNode node);

  /**
   * Rewrites the node using theoryOf to determine which rewriter to use on the node.
   */
  static Node rewrite(Node node);

  /**
   * Rewrites the node using the given theory rewriter.
   */
  static Node rewriteTo(theory::TheoryId theoryId, Node node);

  /**
   * Should be called before the rewriter get's used for the first time.
   */
  static void init();

  /**
   * Should be called to clean up any state.
   */
  static void shutdown();
};

} // Namesapce theory
} // Namespace CVC4
