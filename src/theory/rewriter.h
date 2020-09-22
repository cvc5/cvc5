/*********************                                                        */
/*! \file rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
#include "expr/term_conversion_proof_generator.h"
#include "theory/theory_rewriter.h"
#include "theory/trust_node.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {
namespace theory {

namespace builtin {
class BuiltinProofRuleChecker;
}

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
  friend builtin::BuiltinProofRuleChecker;

 public:
  Rewriter();

  /**
   * Rewrites the node using theoryOf() to determine which rewriter to
   * use on the node.
   */
  static Node rewrite(TNode node);

  /**
   * Rewrites the equality node using theoryOf() to determine which rewriter to
   * use on the node corresponding to an equality s = t.
   *
   * Specifically, this method performs rewrites whose conclusion is not
   * necessarily one of { s = t, t = s, true, false }, which is an invariant
   * guaranted by the above method. This invariant is motivated by theory
   * combination, which needs to guarantee that equalities between terms
   * can be communicated for all pairs of terms.
   */
  static Node rewriteEqualityExt(TNode node);

  /**
   * Rewrite with proof production, which is managed by the term conversion
   * proof generator managed by this class (d_tpg). This method requires a call
   * to setProofNodeManager prior to this call.
   *
   * @param node The node to rewrite.
   * @param elimTheoryRewrite Whether we also want fine-grained proofs for
   * THEORY_REWRITE steps.
   * @param isExtEq Whether node is an equality which we are applying
   * rewriteEqualityExt on.
   * @return The trust node of kind TrustNodeKind::REWRITE that contains the
   * rewritten form of node.
   */
  TrustNode rewriteWithProof(TNode node,
                             bool elimTheoryRewrite = false,
                             bool isExtEq = false);

  /** Set proof node manager */
  void setProofNodeManager(ProofNodeManager* pnm);

  /**
   * Garbage collects the rewrite caches.
   */
  static void clearCaches();

  /**
   * Registers a theory rewriter with this rewriter. The rewriter does not own
   * the theory rewriters.
   *
   * @param tid The theory that the theory rewriter should be associated with.
   * @param trew The theory rewriter to register.
   */
  static void registerTheoryRewriter(theory::TheoryId tid,
                                     TheoryRewriter* trew);

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
   * Get the rewriter associated with the SmtEngine in scope.
   *
   * TODO(#3468): Get rid of this function (it relies on there being an
   * singleton with the current SmtEngine in scope)
   */
  static Rewriter* getInstance();

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
  Node rewriteTo(theory::TheoryId theoryId,
                 Node node,
                 TConvProofGenerator* tcpg = nullptr);

  /** Calls the pre-rewriter for the given theory */
  RewriteResponse preRewrite(theory::TheoryId theoryId,
                             TNode n,
                             TConvProofGenerator* tcpg = nullptr);

  /** Calls the post-rewriter for the given theory */
  RewriteResponse postRewrite(theory::TheoryId theoryId,
                              TNode n,
                              TConvProofGenerator* tcpg = nullptr);
  /** processes a trust rewrite response */
  RewriteResponse processTrustRewriteResponse(
      theory::TheoryId theoryId,
      const TrustRewriteResponse& tresponse,
      bool isPre,
      TConvProofGenerator* tcpg);

  /**
   * Calls the equality-rewriter for the given theory.
   */
  Node callRewriteEquality(theory::TheoryId theoryId, TNode equality);

  void clearCachesInternal();

  /** Theory rewriters used by this rewriter instance */
  TheoryRewriter* d_theoryRewriters[theory::THEORY_LAST];

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

  /** The proof generator */
  std::unique_ptr<TConvProofGenerator> d_tpg;
#ifdef CVC4_ASSERTIONS
  std::unique_ptr<std::unordered_set<Node, NodeHashFunction>> d_rewriteStack =
      nullptr;
#endif /* CVC4_ASSERTIONS */
};/* class Rewriter */

}/* CVC4::theory namespace */
}/* CVC4 namespace */
