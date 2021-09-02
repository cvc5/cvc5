/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Andrew Reynolds, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Rewriter class.
 */

#include "cvc5_private.h"

#pragma once

#include "expr/node.h"
#include "proof/method_id.h"
#include "theory/theory_rewriter.h"

namespace cvc5 {

class TConvProofGenerator;
class ProofNodeManager;
class TrustNode;

namespace theory {

namespace builtin {
class BuiltinProofRuleChecker;
}

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
  Node rewriteEqualityExt(TNode node);

  /**
   * Rewrite with proof production, which is managed by the term conversion
   * proof generator managed by this class (d_tpg). This method requires a call
   * to setProofNodeManager prior to this call.
   *
   * @param node The node to rewrite.
   * @param isExtEq Whether node is an equality which we are applying
   * rewriteEqualityExt on.
   * @return The trust node of kind TrustNodeKind::REWRITE that contains the
   * rewritten form of node.
   */
  TrustNode rewriteWithProof(TNode node,
                             bool isExtEq = false);

  /** Set proof node manager */
  void setProofNodeManager(ProofNodeManager* pnm);

  /** Garbage collects the rewrite caches. */
  void clearCaches();

  /**
   * Registers a theory rewriter with this rewriter. The rewriter does not own
   * the theory rewriters.
   *
   * @param tid The theory that the theory rewriter should be associated with.
   * @param trew The theory rewriter to register.
   */
  void registerTheoryRewriter(theory::TheoryId tid, TheoryRewriter* trew);

  /** Get the theory rewriter for the given id */
  TheoryRewriter* getTheoryRewriter(theory::TheoryId theoryId);

  /**
   * Apply rewrite on n. This encapsulates the exact behavior
   * of a REWRITE step in a proof.
   *
   * @param n The node to rewrite,
   * @param idr The method identifier of the rewriter, by default RW_REWRITE
   * specifying a call to rewrite.
   * @return The rewritten form of n.
   */
  Node rewriteViaMethod(TNode n, MethodId idr = MethodId::RW_REWRITE);

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

  RewriteEnvironment d_re;

  /** The proof generator */
  std::unique_ptr<TConvProofGenerator> d_tpg;
#ifdef CVC5_ASSERTIONS
  std::unique_ptr<std::unordered_set<Node>> d_rewriteStack = nullptr;
#endif /* CVC5_ASSERTIONS */
};/* class Rewriter */

}  // namespace theory
}  // namespace cvc5
