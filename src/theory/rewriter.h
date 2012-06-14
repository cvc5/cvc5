/*********************                                                        */
/*! \file rewriter.h
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
 ** \brief The Rewriter class
 **
 ** The Rewriter class.
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {

/**
 * Theory rewriters signal whether more rewriting is needed (or not)
 * by using a member of this enumeration.  See RewriteResponse, below.
 */
enum RewriteStatus {
  REWRITE_DONE,
  REWRITE_AGAIN,
  REWRITE_AGAIN_FULL
};/* enum RewriteStatus */

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
  RewriteResponse(RewriteStatus status, Node node) :
    status(status), node(node) {}
};/* struct RewriteResponse */

/**
 * The main rewriter class.  All functionality is static.
 */
class Rewriter {

  /** Returns the appropriate cache for a node */
  static Node getPreRewriteCache(theory::TheoryId theoryId, TNode node);

  /** Returns the appropriate cache for a node */
  static Node getPostRewriteCache(theory::TheoryId theoryId, TNode node);

  /** Sets the appropriate cache for a node */
  static void setPreRewriteCache(theory::TheoryId theoryId,
                                 TNode node, TNode cache);

  /** Sets the appropriate cache for a node */
  static void setPostRewriteCache(theory::TheoryId theoryId,
                                  TNode node, TNode cache);

  // disable construction of rewriters; all functionality is static
  Rewriter() CVC4_UNUSED;
  Rewriter(const Rewriter&) CVC4_UNUSED;

  /**
   * Rewrites the node using the given theory rewriter.
   */
  static Node rewriteTo(theory::TheoryId theoryId, Node node);

  /** Calls the pre-rewriter for the given theory */
  static RewriteResponse callPreRewrite(theory::TheoryId theoryId, TNode node);

  /** Calls the post-rewriter for the given theory */
  static RewriteResponse callPostRewrite(theory::TheoryId theoryId, TNode node);

  /**
   * Calls the equality-rewruter for the given theory.
   */
  static Node callRewriteEquality(theory::TheoryId theoryId, TNode equality);

public:


  /**
   * Rewrites the node using theoryOf() to determine which rewriter to
   * use on the node.
   */
  static Node rewrite(TNode node);

  /**
   * Should be called before the rewriter gets used for the first time.
   */
  static void init();

  /**
   * Should be called to clean up any state.
   */
  static void shutdown();


};/* class Rewriter */

}/* CVC4::theory namespace */
}/* CVC4 namespace */
