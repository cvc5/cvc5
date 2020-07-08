/*********************                                                        */
/*! \file theory_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The TheoryRewriter class
 **
 ** The TheoryRewriter class is the interface that theory rewriters implement.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_REWRITER_H
#define CVC4__THEORY__THEORY_REWRITER_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {

class Rewriter;

/**
 * Theory rewriters signal whether more rewriting is needed (or not)
 * by using a member of this enumeration.  See RewriteResponse, below.
 */
enum RewriteStatus
{
  /** The node is fully rewritten (no more rewrites apply) */
  REWRITE_DONE,
  /** The node may be rewritten further */
  REWRITE_AGAIN,
  /** Subnodes of the node may be rewritten further */
  REWRITE_AGAIN_FULL
}; /* enum RewriteStatus */

/**
 * Instances of this class serve as response codes from
 * TheoryRewriter::preRewrite() and TheoryRewriter::postRewrite(). The response
 * consists of the rewritten node as well as a status that indicates whether
 * more rewriting is needed or not.
 */
struct RewriteResponse
{
  const RewriteStatus d_status;
  const Node d_node;
  RewriteResponse(RewriteStatus status, Node n) : d_status(status), d_node(n) {}
}; /* struct RewriteResponse */

/**
 * The interface that a theory rewriter has to implement.
 *
 * Note: A theory rewriter is expected to handle all kinds of a theory, even
 * the ones that are removed by `Theory::expandDefinition()` since it may be
 * called on terms before the definitions have been expanded.
 */
class TheoryRewriter
{
 public:
  virtual ~TheoryRewriter() = default;

  /**
   * Registers the rewrites of a given theory with the rewriter.
   *
   * @param rewriter The rewriter to register the rewrites with.
   */
  virtual void registerRewrites(Rewriter* rewriter) {}

  /**
   * Performs a pre-rewrite step.
   *
   * @param node The node to rewrite
   */
  virtual RewriteResponse postRewrite(TNode node) = 0;

  /**
   * Performs a post-rewrite step.
   *
   * @param node The node to rewrite
   */
  virtual RewriteResponse preRewrite(TNode node) = 0;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__THEORY_REWRITER_H */
