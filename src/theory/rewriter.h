/*********************                                                        */
/*! \file rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Rewriter class
 **
 ** The Rewriter class.
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "theory/theory_rewriter.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {
namespace theory {

class RewriterInitializer;

/**
 * The rewrite environment holds everything that the individual rewrites have
 * access to.
 */
class RewriteEnvironment
{
};

/**
 * The identity rewrite just returns the original node.
 *
 * @param re The rewrite environment
 * @param n The node to rewrite
 * @return The original node
 */
RewriteResponse identityRewrite(RewriteEnvironment* re, TNode n);

/**
 * The main rewriter class.
 */
class Rewriter {
 public:
  Rewriter();

  /**
   * Rewrites the node using theoryOf() to determine which rewriter to
   * use on the node.
   */
  static Node rewrite(TNode node);

  /**
   * Garbage collects the rewrite caches.
   */
  static void clearCaches();

  /**
   * Register a prerewrite for a given kind.
   *
   * @param k The kind to register a rewrite for.
   * @param fn The function that performs the rewrite.
   */
  void registerPreRewrite(
      Kind k, std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn);

  /**
   * Register a postrewrite for a given kind.
   *
   * @param k The kind to register a rewrite for.
   * @param fn The function that performs the rewrite.
   */
  void registerPostRewrite(
      Kind k, std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn);

  /**
   * Register a prerewrite for equalities belonging to a given theory.
   *
   * @param tid The theory to register a rewrite for.
   * @param fn The function that performs the rewrite.
   */
  void registerPreRewriteEqual(
      theory::TheoryId tid,
      std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn);

  /**
   * Register a postrewrite for equalities belonging to a given theory.
   *
   * @param tid The theory to register a rewrite for.
   * @param fn The function that performs the rewrite.
   */
  void registerPostRewriteEqual(
      theory::TheoryId tid,
      std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn);

 private:
  /**
   * Get the (singleton) instance of the rewriter.
   *
   * TODO(#3468): Get rid of this singleton
   */
  static Rewriter& getInstance();

  /** Returns the appropriate cache for a node */
  Node getPreRewriteCache(theory::TheoryId theoryId, TNode node);

  /** Returns the appropriate cache for a node */
  Node getPostRewriteCache(theory::TheoryId theoryId, TNode node);

  /** Sets the appropriate cache for a node */
  void setPreRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache);

  /** Sets the appropriate cache for a node */
  void setPostRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache);

  /**
   * Rewrites the node using the given theory rewriter.
   */
  Node rewriteTo(theory::TheoryId theoryId, Node node);

  /** Calls the pre-rewriter for the given theory */
  RewriteResponse preRewrite(theory::TheoryId theoryId, TNode n);

  /** Calls the post-rewriter for the given theory */
  RewriteResponse postRewrite(theory::TheoryId theoryId, TNode n);

  /**
   * Calls the equality-rewriter for the given theory.
   */
  Node callRewriteEquality(theory::TheoryId theoryId, TNode equality);

  void clearCachesInternal();

  /** Theory rewriters managed by this rewriter instance */
  std::unique_ptr<TheoryRewriter> d_theoryRewriters[theory::THEORY_LAST];

  unsigned long d_iterationCount = 0;

  /** Rewriter table for prewrites. Maps kinds to rewriter function. */
  std::function<RewriteResponse(RewriteEnvironment*, TNode)>
      d_preRewriters[kind::LAST_KIND];
  /** Rewriter table for postrewrites. Maps kinds to rewriter function. */
  std::function<RewriteResponse(RewriteEnvironment*, TNode)>
      d_postRewriters[kind::LAST_KIND];
  /**
   * Rewriter table for prerewrites of equalities. Maps theory to rewriter
   * function.
   */
  std::function<RewriteResponse(RewriteEnvironment*, TNode)>
      d_preRewritersEqual[theory::THEORY_LAST];
  /**
   * Rewriter table for postrewrites of equalities. Maps theory to rewriter
   * function.
   */
  std::function<RewriteResponse(RewriteEnvironment*, TNode)>
      d_postRewritersEqual[theory::THEORY_LAST];

  RewriteEnvironment d_re;

#ifdef CVC4_ASSERTIONS
  std::unique_ptr<std::unordered_set<Node, NodeHashFunction>> d_rewriteStack =
      nullptr;
#endif /* CVC4_ASSERTIONS */
};/* class Rewriter */

}/* CVC4::theory namespace */
}/* CVC4 namespace */
