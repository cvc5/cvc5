/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Rewriter class.
 */

#include "theory/rewriter.h"

#include <deque>

#include "options/theory_options.h"
#include "proof/conv_proof_generator.h"
#include "theory/builtin/proof_checker.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/rewriter_tables.h"
#include "theory/theory.h"
#include "util/resource_manager.h"

using namespace std;

namespace cvc5::internal {
namespace theory {

// Note that this function is a simplified version of Theory::theoryOf for
// (type-based) theoryOfMode. We expand and simplify it here for the sake of
// efficiency.
static TheoryId theoryOf(TNode node)
{
  if (node.getKind() == Kind::EQUAL)
  {
    // Equality is owned by the theory that owns the domain
    return Theory::theoryOf(node[0].getType());
  }
  // Regular nodes are owned by the kind
  return kindToTheoryId(node.getKind());
}

/**
 * TheoryEngine::rewrite() keeps a stack of things that are being pre-
 * and post-rewritten.  Each element of the stack is a
 * RewriteStackElement.
 */
struct RewriteStackElement
{
  enum State
  {
    PRE_REWRITE,
    REWRITE_CHILDREN,
    POST_REWRITE,
    WAIT_FOR_FULL_REWRITE,
    FINALIZE
  };

  /**
   * Construct a fresh stack element.
   */
  RewriteStackElement(TNode node, TheoryId theoryId)
      : d_node(node),
        d_original(node),
        d_postRewriteCache(Node::null()),
        d_fullRewriteNode(Node::null()),
        d_theoryId(theoryId),
        d_originalTheoryId(theoryId),
        d_state(PRE_REWRITE),
        d_nextChild(0),
        d_builder(node.getNodeManager())
  {
  }

  TheoryId getTheoryId() { return static_cast<TheoryId>(d_theoryId); }

  TheoryId getOriginalTheoryId()
  {
    return static_cast<TheoryId>(d_originalTheoryId);
  }

  State getState() const { return static_cast<State>(d_state); }

  void setState(State state) { d_state = state; }

  /** The node we're currently rewriting */
  Node d_node;
  /** Original node (either the unrewritten node or the node after prerewriting)
   */
  Node d_original;
  /** Cached post-rewrite result, if one exists for d_original */
  Node d_postRewriteCache;
  /** Node whose full rewrite this stack element is waiting on */
  Node d_fullRewriteNode;
  /** Id of the theory that's currently rewriting this node */
  unsigned d_theoryId : 8;
  /** Id of the original theory that started the rewrite */
  unsigned d_originalTheoryId : 8;
  /** The current processing state for this node */
  unsigned d_state : 8;
  /** Index of the child this node is done rewriting */
  unsigned d_nextChild : 32;
  /** Builder for this node */
  NodeBuilder d_builder;
};

Node Rewriter::rewrite(TNode node)
{
  if (node.getNumChildren() == 0)
  {
    // Nodes with zero children should never change via rewriting. We return
    // eagerly for the sake of efficiency here.
    return node;
  }
  return rewriteTo(theoryOf(node), node);
}

Node Rewriter::extendedRewrite(TNode node, bool aggr)
{
  quantifiers::ExtendedRewriter er(d_nm, *this, aggr);
  return er.extendedRewrite(node);
}

TrustNode Rewriter::rewriteWithProof(TNode node, bool isExtEq)
{
  // must set the proof checker before calling this
  Assert(d_tpg != nullptr);
  if (isExtEq)
  {
    // theory rewriter is responsible for rewriting the equality
    TheoryRewriter* tr = d_theoryRewriters[theoryOf(node)];
    Assert(tr != nullptr);
    return tr->rewriteEqualityExtWithProof(node);
  }
  Node ret = rewriteTo(theoryOf(node), node, d_tpg.get());
  return TrustNode::mkTrustRewrite(node, ret, d_tpg.get());
}

void Rewriter::finishInit(Env& env)
{
  // if not already initialized with proof support
  if (d_tpg == nullptr)
  {
    Trace("rewriter") << "Rewriter::finishInit" << std::endl;
    // the rewriter is staticly determinstic, thus use static cache policy
    // for the term conversion proof generator
    d_tpg.reset(new TConvProofGenerator(env,
                                        nullptr,
                                        TConvPolicy::FIXPOINT,
                                        TConvCachePolicy::STATIC,
                                        "Rewriter::TConvProofGenerator"));
  }
}

Node Rewriter::rewriteEqualityExt(TNode node)
{
  Assert(node.getKind() == Kind::EQUAL);
  // note we don't force caching of this method currently
  return d_theoryRewriters[theoryOf(node)]->rewriteEqualityExt(node);
}

void Rewriter::registerTheoryRewriter(theory::TheoryId tid,
                                      TheoryRewriter* trew)
{
  if (trew == nullptr)
  {
    // if nullptr, use the default (null) theory rewriter.
    d_nullTr.emplace_back(
        std::unique_ptr<NoOpTheoryRewriter>(new NoOpTheoryRewriter(d_nm, tid)));
    d_theoryRewriters[tid] = d_nullTr.back().get();
  }
  else
  {
    d_theoryRewriters[tid] = trew;
  }
}

TheoryRewriter* Rewriter::getTheoryRewriter(theory::TheoryId theoryId)
{
  return d_theoryRewriters[theoryId];
}

Node Rewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  // dispatches to the appropriate theory
  TheoryId tid = theoryOf(n);
  TheoryRewriter* tr = getTheoryRewriter(tid);
  if (tr != nullptr)
  {
    return tr->rewriteViaRule(id, n);
  }
  return Node::null();
}

ProofRewriteRule Rewriter::findRule(const Node& a,
                                    const Node& b,
                                    TheoryRewriteCtx ctx)
{
  // dispatches to the appropriate theory
  TheoryId tid = theoryOf(a);
  TheoryRewriter* tr = getTheoryRewriter(tid);
  if (tr != nullptr)
  {
    return tr->findRule(a, b, ctx);
  }
  return ProofRewriteRule::NONE;
}

Node Rewriter::rewriteTo(theory::TheoryId theoryId,
                         Node node,
                         TConvProofGenerator* tcpg)
{
#ifdef CVC5_ASSERTIONS
  bool isEquality = node.getKind() == Kind::EQUAL
                    && !node[0].getType().isBoolean()
                    && !node[1].getType().isBoolean();

  if (d_rewriteStack == nullptr)
  {
    d_rewriteStack.reset(new std::unordered_set<Node>());
  }
#endif

  Trace("rewriter") << "Rewriter::rewriteTo(" << theoryId << "," << node << ")"
                    << std::endl;

  // Check if it's been cached already
  Node cached = getPostRewriteCache(theoryId, node);
  if (!cached.isNull() && (tcpg == nullptr || hasRewrittenWithProofs(node)))
  {
    return cached;
  }

  // Put the node on the stack in order to start the "recursive" rewrite
  // Use deque since RewriteStackElement contains a live NodeBuilder; unlike a
  // vector, pushing deep stacks will not relocate existing frames.
  deque<RewriteStackElement> rewriteStack;
  rewriteStack.push_back(RewriteStackElement(node, theoryId));

  // Rewrite until the stack is empty
  for (;;)
  {
    if (d_resourceManager != nullptr)
    {
      d_resourceManager->spendResource(Resource::RewriteStep);
    }

    // Get the top of the recursion stack
    RewriteStackElement& rewriteStackTop = rewriteStack.back();

    Trace("rewriter") << "Rewriter::rewriting: "
                      << rewriteStackTop.getTheoryId() << ","
                      << rewriteStackTop.d_node << std::endl;

    RewriteStackElement::State state = rewriteStackTop.getState();
    if (state == RewriteStackElement::PRE_REWRITE)
    {
      // Check if the pre-rewrite has already been done (it's in the cache)
      cached = getPreRewriteCache(rewriteStackTop.getTheoryId(),
                                  rewriteStackTop.d_node);
      if (cached.isNull()
          || (tcpg != nullptr
              && !hasRewrittenWithProofs(rewriteStackTop.d_node)))
      {
        // Rewrite until fix-point is reached
        for (;;)
        {
          // Perform the pre-rewrite
          Kind originalKind = rewriteStackTop.d_node.getKind();
          RewriteResponse response = preRewrite(
              rewriteStackTop.getTheoryId(), rewriteStackTop.d_node, tcpg);

          // Put the rewritten node to the top of the stack
          TNode newNode = response.d_node;
          Trace("rewriter-debug") << "Pre-Rewrite: " << rewriteStackTop.d_node
                                  << " to " << newNode << std::endl;
          TheoryId newTheory = theoryOf(newNode);
          rewriteStackTop.d_node = newNode;
          rewriteStackTop.d_theoryId = newTheory;
          Assert(newNode.getType().isComparableTo(
              rewriteStackTop.d_node.getType()))
              << "Pre-rewriting " << rewriteStackTop.d_node << " to " << newNode
              << " does not preserve type";
          // In the pre-rewrite, if changing theories, we just call the other
          // theories pre-rewrite. If the kind of the node was changed, then we
          // pre-rewrite again.
          if ((originalKind == newNode.getKind()
               && response.d_status == REWRITE_DONE)
              || newNode.getNumChildren() == 0)
          {
            if (Configuration::isAssertionBuild())
            {
              // REWRITE_DONE should imply that no other pre-rewriting can be
              // done.
              Node rewrittenAgain =
                  preRewrite(newTheory, newNode, nullptr).d_node;
              Assert(newNode == rewrittenAgain)
                  << "Rewriter returned REWRITE_DONE for " << newNode
                  << " but it can be rewritten to " << rewrittenAgain;
            }
            break;
          }
        }

        // Cache the rewrite
        setPreRewriteCache(rewriteStackTop.getOriginalTheoryId(),
                           rewriteStackTop.d_original,
                           rewriteStackTop.d_node);
      }
      // Otherwise we've already been pre-rewritten (in pre-rewrite cache)
      else
      {
        // Continue with the cached version
        rewriteStackTop.d_node = cached;
        rewriteStackTop.d_theoryId = theoryOf(cached);
      }
      rewriteStackTop.d_original = rewriteStackTop.d_node;
      rewriteStackTop.d_postRewriteCache = getPostRewriteCache(
          rewriteStackTop.getTheoryId(), rewriteStackTop.d_node);
      if (!rewriteStackTop.d_postRewriteCache.isNull()
          && (tcpg == nullptr
              || hasRewrittenWithProofs(rewriteStackTop.d_node)))
      {
        rewriteStackTop.d_node = rewriteStackTop.d_postRewriteCache;
        rewriteStackTop.d_theoryId = theoryOf(rewriteStackTop.d_node);
        rewriteStackTop.setState(RewriteStackElement::FINALIZE);
      }
      else
      {
        rewriteStackTop.setState(RewriteStackElement::REWRITE_CHILDREN);
      }
      continue;
    }

    if (state == RewriteStackElement::REWRITE_CHILDREN)
    {
      size_t numChildren = rewriteStackTop.d_node.getNumChildren();
      if (rewriteStackTop.d_nextChild == 0 && numChildren > 0)
      {
        // The children will add themselves to the builder once they're done.
        rewriteStackTop.d_builder << rewriteStackTop.d_node.getKind();
        kind::MetaKind metaKind = rewriteStackTop.d_node.getMetaKind();
        if (metaKind == kind::metakind::PARAMETERIZED)
        {
          rewriteStackTop.d_builder << rewriteStackTop.d_node.getOperator();
        }
      }
      if (rewriteStackTop.d_nextChild < numChildren)
      {
        Node childNode = rewriteStackTop.d_node[rewriteStackTop.d_nextChild++];
        rewriteStack.push_back(
            RewriteStackElement(childNode, theoryOf(childNode)));
        continue;
      }
      if (numChildren > 0)
      {
        rewriteStackTop.d_node = rewriteStackTop.d_builder;
        rewriteStackTop.d_theoryId = theoryOf(rewriteStackTop.d_node);
      }
      rewriteStackTop.setState(RewriteStackElement::POST_REWRITE);
      continue;
    }

    if (state == RewriteStackElement::POST_REWRITE)
    {
      bool pushedFullRewrite = false;
      for (;;)
      {
        // Do the post-rewrite
        Kind originalKind = rewriteStackTop.d_node.getKind();
        RewriteResponse response = postRewrite(
            rewriteStackTop.getTheoryId(), rewriteStackTop.d_node, tcpg);
        TNode newNode = response.d_node;
        Trace("rewriter-debug") << "Post-Rewrite: " << rewriteStackTop.d_node
                                << " to " << newNode << std::endl;
        TheoryId newTheoryId = theoryOf(newNode);
        Assert(
            newNode.getType().isComparableTo(rewriteStackTop.d_node.getType()))
            << "Post-rewriting " << rewriteStackTop.d_node << " to " << newNode
            << " does not preserve type";
        if (newTheoryId != rewriteStackTop.getTheoryId()
            || response.d_status == REWRITE_AGAIN_FULL)
        {
          // In the post rewrite if we've changed theories, do the full rewrite
          // by pushing it onto the explicit stack instead of recursing.
          Assert(response.d_node != rewriteStackTop.d_node);
          // TODO: this is not thread-safe - should make this assertion
          // dependent on sequential build
#ifdef CVC5_ASSERTIONS
          Assert(d_rewriteStack->find(response.d_node) == d_rewriteStack->end())
              << "Non-terminating rewriting detected for: " << response.d_node;
          d_rewriteStack->insert(response.d_node);
#endif
          rewriteStackTop.d_fullRewriteNode = response.d_node;
          rewriteStackTop.setState(RewriteStackElement::WAIT_FOR_FULL_REWRITE);
          rewriteStack.push_back(
              RewriteStackElement(response.d_node, newTheoryId));
          pushedFullRewrite = true;
          break;
        }
        else if ((response.d_status == REWRITE_DONE
                  && originalKind == newNode.getKind())
                 || newNode.getNumChildren() == 0)
        {
#ifdef CVC5_ASSERTIONS
          RewriteResponse r2 =
              d_theoryRewriters[newTheoryId]->postRewrite(newNode);
          Assert(r2.d_node == newNode)
              << "Non-idempotent rewriting: " << r2.d_node << " != " << newNode;
#endif
          rewriteStackTop.d_node = newNode;
          rewriteStackTop.d_theoryId = newTheoryId;
          rewriteStackTop.setState(RewriteStackElement::FINALIZE);
          break;
        }
        // Check for trivial rewrite loops of size 1 or 2
        Assert(response.d_node != rewriteStackTop.d_node);
        Assert(d_theoryRewriters[rewriteStackTop.getTheoryId()]
                   ->postRewrite(response.d_node)
                   .d_node
               != rewriteStackTop.d_node);
        rewriteStackTop.d_node = response.d_node;
        rewriteStackTop.d_theoryId = newTheoryId;
      }
      continue;
    }

    if (state == RewriteStackElement::FINALIZE)
    {
      // We're done with the post rewrite, so we add to the cache.
      if (tcpg != nullptr)
      {
        // if proofs are enabled, mark that we've rewritten with proofs
        d_tpgNodes.insert(rewriteStackTop.d_original);
        if (!rewriteStackTop.d_postRewriteCache.isNull())
        {
          // We may have gotten a different node, due to non-determinism in
          // theory rewriters (e.g. quantifiers rewriter which introduces
          // fresh BOUND_VARIABLE). This can happen if we wrote once without
          // proofs and then rewrote again with proofs.
          if (rewriteStackTop.d_node != rewriteStackTop.d_postRewriteCache)
          {
            Trace("rewriter-proof") << "WARNING: Rewritten forms with and "
                                       "without proofs were not equivalent"
                                    << std::endl;
            Trace("rewriter-proof")
                << "   original: " << rewriteStackTop.d_original << std::endl;
            Trace("rewriter-proof")
                << "with proofs: " << rewriteStackTop.d_node << std::endl;
            Trace("rewriter-proof")
                << " w/o proofs: " << rewriteStackTop.d_postRewriteCache
                << std::endl;
            Node eq = rewriteStackTop.d_node.eqNode(
                rewriteStackTop.d_postRewriteCache);
            // we make this a post-rewrite, since we are processing a node that
            // has finished post-rewriting above
            Node trrid = mkTrustId(d_nm, TrustId::REWRITE_NO_ELABORATE);
            tcpg->addRewriteStep(rewriteStackTop.d_node,
                                 rewriteStackTop.d_postRewriteCache,
                                 ProofRule::TRUST,
                                 {},
                                 {trrid, eq},
                                 false);
            // don't overwrite the cache, should be the same
            rewriteStackTop.d_node = rewriteStackTop.d_postRewriteCache;
          }
        }
      }
      setPostRewriteCache(rewriteStackTop.getOriginalTheoryId(),
                          rewriteStackTop.d_original,
                          rewriteStackTop.d_node);

      // If this is the last node, just return.
      if (rewriteStack.size() == 1)
      {
        Assert(!isEquality || rewriteStackTop.d_node.getKind() == Kind::EQUAL
               || rewriteStackTop.d_node.isConst());
        Assert(rewriteStackTop.d_node.getType().isComparableTo(node.getType()))
            << "Rewriting " << node << " to " << rewriteStackTop.d_node
            << " does not preserve type";
        return rewriteStackTop.d_node;
      }

      RewriteStackElement& parent = rewriteStack[rewriteStack.size() - 2];
      if (parent.getState() == RewriteStackElement::WAIT_FOR_FULL_REWRITE)
      {
#ifdef CVC5_ASSERTIONS
        d_rewriteStack->erase(parent.d_fullRewriteNode);
#endif
        parent.d_node = rewriteStackTop.d_node;
        parent.d_theoryId = theoryOf(parent.d_node);
        parent.d_fullRewriteNode = Node::null();
        // Resume the parent's post-rewrite fixpoint on the fully rewritten
        // node. This preserves the recursive behavior where a full rewrite
        // requested from post-rewrite returns to post-rewrite, and only
        // finalizes once post-rewriting is done.
        parent.setState(RewriteStackElement::POST_REWRITE);
      }
      else
      {
        parent.d_builder << rewriteStackTop.d_node;
      }
      rewriteStack.pop_back();
      continue;
    }

    Assert(state == RewriteStackElement::WAIT_FOR_FULL_REWRITE);
  }

  Unreachable();
} /* Rewriter::rewriteTo() */

RewriteResponse Rewriter::preRewrite(theory::TheoryId theoryId,
                                     TNode n,
                                     TConvProofGenerator* tcpg)
{
  if (tcpg != nullptr)
  {
    // call the trust rewrite response interface
    TrustRewriteResponse tresponse =
        d_theoryRewriters[theoryId]->preRewriteWithProof(n);
    // process the trust rewrite response: store the proof step into
    // tcpg if necessary and then convert to rewrite response.
    return processTrustRewriteResponse(theoryId, tresponse, true, tcpg);
  }
  return d_theoryRewriters[theoryId]->preRewrite(n);
}

RewriteResponse Rewriter::postRewrite(theory::TheoryId theoryId,
                                      TNode n,
                                      TConvProofGenerator* tcpg)
{
  if (tcpg != nullptr)
  {
    // same as above, for post-rewrite
    TrustRewriteResponse tresponse =
        d_theoryRewriters[theoryId]->postRewriteWithProof(n);
    return processTrustRewriteResponse(theoryId, tresponse, false, tcpg);
  }
  return d_theoryRewriters[theoryId]->postRewrite(n);
}

RewriteResponse Rewriter::processTrustRewriteResponse(
    theory::TheoryId theoryId,
    const TrustRewriteResponse& tresponse,
    bool isPre,
    TConvProofGenerator* tcpg)
{
  Assert(tcpg != nullptr);
  TrustNode trn = tresponse.d_node;
  Assert(trn.getKind() == TrustNodeKind::REWRITE);
  Node proven = trn.getProven();
  if (proven[0] != proven[1])
  {
    ProofGenerator* pg = trn.getGenerator();
    if (pg == nullptr)
    {
      Node tidn =
          builtin::BuiltinProofRuleChecker::mkTheoryIdNode(d_nm, theoryId);
      // add small step trusted rewrite
      Node rid = mkMethodId(d_nm,
                            isPre ? MethodId::RW_REWRITE_THEORY_PRE
                                  : MethodId::RW_REWRITE_THEORY_POST);
      tcpg->addRewriteStep(proven[0],
                           proven[1],
                           ProofRule::TRUST_THEORY_REWRITE,
                           {},
                           {proven, tidn, rid},
                           isPre);
    }
    else
    {
      // store proven rewrite step
      tcpg->addRewriteStep(proven[0], proven[1], pg, isPre);
    }
  }
  return RewriteResponse(tresponse.d_status, trn.getNode());
}

bool Rewriter::hasRewrittenWithProofs(TNode n) const
{
  return d_tpgNodes.find(n) != d_tpgNodes.end();
}

}  // namespace theory
}  // namespace cvc5::internal
