/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/theory_rewriter.h"

namespace cvc5::internal {

class Env;
class TConvProofGenerator;
class ProofNodeManager;
class TrustNode;

namespace theory {

class Evaluator;

/**
 * The main rewriter class.
 */
class Rewriter {
  friend class cvc5::internal::Env;  // to set the resource manager
 public:
  Rewriter();

  /**
   * Rewrites the node using theoryOf() to determine which rewriter to
   * use on the node.
   */
  Node rewrite(TNode node);

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
   * !!! Temporary until static access to rewriter is eliminated. This method
   * should be moved to same place as evaluate (currently in Env).
   *
   * Extended rewrite of the given node. This method is implemented by a
   * custom ExtendRewriter class that wraps this class to perform custom
   * rewrites (usually those that are not useful for solving, but e.g. useful
   * for SyGuS symmetry breaking).
   * @param node The node to rewrite
   * @param aggr Whether to perform aggressive rewrites.
   */
  Node extendedRewrite(TNode node, bool aggr = true);

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

  /** Finish init, which sets up the proof manager if applicable */
  void finishInit(Env& env);

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

 private:

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

  /**
   * Has n been rewritten with proofs? This checks if n is in d_tpgNodes.
   */
  bool hasRewrittenWithProofs(TNode n) const;

  /** The resource manager, for tracking resource usage */
  ResourceManager* d_resourceManager;

  /** Theory rewriters used by this rewriter instance */
  TheoryRewriter* d_theoryRewriters[theory::THEORY_LAST];

  /** The proof generator */
  std::unique_ptr<TConvProofGenerator> d_tpg;
  /**
   * Nodes rewritten with proofs. Since d_tpg contains a reference to all
   * nodes that have been rewritten with proofs, we can keep only a TNode
   * here.
   */
  std::unordered_set<TNode> d_tpgNodes;
#ifdef CVC5_ASSERTIONS
  std::unique_ptr<std::unordered_set<Node>> d_rewriteStack = nullptr;
#endif /* CVC5_ASSERTIONS */
};/* class Rewriter */

}  // namespace theory
}  // namespace cvc5::internal
