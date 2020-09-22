/*********************                                                        */
/*! \file rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/rewriter.h"

#include "options/theory_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter_tables.h"
#include "theory/theory.h"
#include "util/resource_manager.h"

using namespace std;

namespace CVC4 {
namespace theory {

// Note that this function is a simplified version of Theory::theoryOf for
// (type-based) theoryOfMode. We expand and simplify it here for the sake of
// efficiency.
static TheoryId theoryOf(TNode node) {
  if (node.getKind() == kind::EQUAL)
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
struct RewriteStackElement {
  /**
   * Construct a fresh stack element.
   */
  RewriteStackElement(TNode node, TheoryId theoryId)
      : d_node(node),
        d_original(node),
        d_theoryId(theoryId),
        d_originalTheoryId(theoryId),
        d_nextChild(0)
  {
  }

  TheoryId getTheoryId() { return static_cast<TheoryId>(d_theoryId); }

  TheoryId getOriginalTheoryId()
  {
    return static_cast<TheoryId>(d_originalTheoryId);
  }

  /** The node we're currently rewriting */
  Node d_node;
  /** Original node (either the unrewritten node or the node after prerewriting)
   */
  Node d_original;
  /** Id of the theory that's currently rewriting this node */
  unsigned d_theoryId : 8;
  /** Id of the original theory that started the rewrite */
  unsigned d_originalTheoryId : 8;
  /** Index of the child this node is done rewriting */
  unsigned d_nextChild : 32;
  /** Builder for this node */
  NodeBuilder<> d_builder;
};

RewriteResponse identityRewrite(RewriteEnvironment* re, TNode n)
{
  return RewriteResponse(REWRITE_DONE, n);
}

Node Rewriter::rewrite(TNode node) {
  if (node.getNumChildren() == 0)
  {
    // Nodes with zero children should never change via rewriting. We return
    // eagerly for the sake of efficiency here.
    return node;
  }
  return getInstance()->rewriteTo(theoryOf(node), node);
}

TrustNode Rewriter::rewriteWithProof(TNode node,
                                     bool elimTheoryRewrite,
                                     bool isExtEq)
{
  // must set the proof checker before calling this
  Assert(d_tpg != nullptr);
  if (isExtEq)
  {
    // theory rewriter is responsible for rewriting the equality
    TheoryRewriter* tr = getInstance()->d_theoryRewriters[theoryOf(node)];
    Assert(tr != nullptr);
    return tr->rewriteEqualityExtWithProof(node);
  }
  Node ret = getInstance()->rewriteTo(theoryOf(node), node, d_tpg.get());
  return TrustNode::mkTrustRewrite(node, ret, d_tpg.get());
}

void Rewriter::setProofNodeManager(ProofNodeManager* pnm)
{
  // if not already initialized with proof support
  if (d_tpg == nullptr)
  {
    // the rewriter is staticly determinstic, thus use static cache policy
    // for the term conversion proof generator
    d_tpg.reset(new TConvProofGenerator(pnm,
                                        nullptr,
                                        TConvPolicy::FIXPOINT,
                                        TConvCachePolicy::STATIC,
                                        "Rewriter::TConvProofGenerator"));
  }
}

Node Rewriter::rewriteEqualityExt(TNode node)
{
  Assert(node.getKind() == kind::EQUAL);
  // note we don't force caching of this method currently
  return getInstance()->d_theoryRewriters[theoryOf(node)]->rewriteEqualityExt(
      node);
}

void Rewriter::registerTheoryRewriter(theory::TheoryId tid,
                                      TheoryRewriter* trew)
{
  getInstance()->d_theoryRewriters[tid] = trew;
}

void Rewriter::registerPreRewrite(
    Kind k, std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn)
{
  Assert(k != kind::EQUAL) << "Register pre-rewrites for EQUAL with registerPreRewriteEqual.";
  d_preRewriters[k] = fn;
}

void Rewriter::registerPostRewrite(
    Kind k, std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn)
{
  Assert(k != kind::EQUAL) << "Register post-rewrites for EQUAL with registerPostRewriteEqual.";
  d_postRewriters[k] = fn;
}

void Rewriter::registerPreRewriteEqual(
    theory::TheoryId tid,
    std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn)
{
  d_preRewritersEqual[tid] = fn;
}

void Rewriter::registerPostRewriteEqual(
    theory::TheoryId tid,
    std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn)
{
  d_postRewritersEqual[tid] = fn;
}

Rewriter* Rewriter::getInstance()
{
  return smt::currentSmtEngine()->getRewriter();
}

Node Rewriter::rewriteTo(theory::TheoryId theoryId,
                         Node node,
                         TConvProofGenerator* tcpg)
{
#ifdef CVC4_ASSERTIONS
  bool isEquality = node.getKind() == kind::EQUAL && (!node[0].getType().isBoolean());

  if (d_rewriteStack == nullptr)
  {
    d_rewriteStack.reset(new std::unordered_set<Node, NodeHashFunction>());
  }
#endif

  Trace("rewriter") << "Rewriter::rewriteTo(" << theoryId << "," << node << ")"<< std::endl;

  // Check if it's been cached already
  Node cached = getPostRewriteCache(theoryId, node);
  if (!cached.isNull() && (tcpg == nullptr || tcpg->hasRewriteStep(node)))
  {
    return cached;
  }

  // Put the node on the stack in order to start the "recursive" rewrite
  vector<RewriteStackElement> rewriteStack;
  rewriteStack.push_back(RewriteStackElement(node, theoryId));

  ResourceManager* rm = NULL;
  bool hasSmtEngine = smt::smtEngineInScope();
  if (hasSmtEngine) {
    rm = smt::currentResourceManager();
  }
  // Rewrite until the stack is empty
  for (;;){

    if (hasSmtEngine &&
		d_iterationCount % ResourceManager::getFrequencyCount() == 0) {
      rm->spendResource(ResourceManager::Resource::RewriteStep);
      d_iterationCount = 0;
    }

    // Get the top of the recursion stack
    RewriteStackElement& rewriteStackTop = rewriteStack.back();

    Trace("rewriter") << "Rewriter::rewriting: "
                      << rewriteStackTop.getTheoryId() << ","
                      << rewriteStackTop.d_node << std::endl;

    // Before rewriting children we need to do a pre-rewrite of the node
    if (rewriteStackTop.d_nextChild == 0)
    {
      // Check if the pre-rewrite has already been done (it's in the cache)
      cached = getPreRewriteCache(rewriteStackTop.getTheoryId(),
                                  rewriteStackTop.d_node);
      if (cached.isNull()
          || (tcpg != nullptr && !tcpg->hasRewriteStep(rewriteStackTop.d_node)))
      {
        // Rewrite until fix-point is reached
        for(;;) {
          // Perform the pre-rewrite
          RewriteResponse response = preRewrite(
              rewriteStackTop.getTheoryId(), rewriteStackTop.d_node, tcpg);

          // Put the rewritten node to the top of the stack
          rewriteStackTop.d_node = response.d_node;
          TheoryId newTheory = theoryOf(rewriteStackTop.d_node);
          // In the pre-rewrite, if changing theories, we just call the other theories pre-rewrite
          if (newTheory == rewriteStackTop.getTheoryId()
              && response.d_status == REWRITE_DONE)
          {
            break;
          }
          rewriteStackTop.d_theoryId = newTheory;
        }

        // Cache the rewrite
        setPreRewriteCache(rewriteStackTop.getOriginalTheoryId(),
                           rewriteStackTop.d_original,
                           rewriteStackTop.d_node);
      }
      // Otherwise we're have already been pre-rewritten (in pre-rewrite cache)
      else {
        // Continue with the cached version
        rewriteStackTop.d_node = cached;
        rewriteStackTop.d_theoryId = theoryOf(cached);
      }
    }

    rewriteStackTop.d_original = rewriteStackTop.d_node;
    // Now it's time to rewrite the children, check if this has already been done
    cached = getPostRewriteCache(rewriteStackTop.getTheoryId(),
                                 rewriteStackTop.d_node);
    // If not, go through the children
    if (cached.isNull()
        || (tcpg != nullptr && !tcpg->hasRewriteStep(rewriteStackTop.d_node)))
    {
      // The child we need to rewrite
      unsigned child = rewriteStackTop.d_nextChild++;

      // To build the rewritten expression we set up the builder
      if(child == 0) {
        if (rewriteStackTop.d_node.getNumChildren() > 0)
        {
          // The children will add themselves to the builder once they're done
          rewriteStackTop.d_builder << rewriteStackTop.d_node.getKind();
          kind::MetaKind metaKind = rewriteStackTop.d_node.getMetaKind();
          if (metaKind == kind::metakind::PARAMETERIZED) {
            rewriteStackTop.d_builder << rewriteStackTop.d_node.getOperator();
          }
        }
      }

      // Process the next child
      if (child < rewriteStackTop.d_node.getNumChildren())
      {
        // The child node
        Node childNode = rewriteStackTop.d_node[child];
        // Push the rewrite request to the stack (NOTE: rewriteStackTop might be a bad reference now)
        rewriteStack.push_back(RewriteStackElement(childNode, theoryOf(childNode)));
        // Go on with the rewriting
        continue;
      }

      // Incorporate the children if necessary
      if (rewriteStackTop.d_node.getNumChildren() > 0)
      {
        Node rewritten = rewriteStackTop.d_builder;
        rewriteStackTop.d_node = rewritten;
        rewriteStackTop.d_theoryId = theoryOf(rewriteStackTop.d_node);
      }

      // Done with all pre-rewriting, so let's do the post rewrite
      for(;;) {
        // Do the post-rewrite
        RewriteResponse response = postRewrite(
            rewriteStackTop.getTheoryId(), rewriteStackTop.d_node, tcpg);

        // We continue with the response we got
        TheoryId newTheoryId = theoryOf(response.d_node);
        if (newTheoryId != rewriteStackTop.getTheoryId()
            || response.d_status == REWRITE_AGAIN_FULL)
        {
          // In the post rewrite if we've changed theories, we must do a full rewrite
          Assert(response.d_node != rewriteStackTop.d_node);
          //TODO: this is not thread-safe - should make this assertion dependent on sequential build
#ifdef CVC4_ASSERTIONS
          Assert(d_rewriteStack->find(response.d_node)
                 == d_rewriteStack->end());
          d_rewriteStack->insert(response.d_node);
#endif
          Node rewritten = rewriteTo(newTheoryId, response.d_node, tcpg);
          rewriteStackTop.d_node = rewritten;
#ifdef CVC4_ASSERTIONS
          d_rewriteStack->erase(response.d_node);
#endif
          break;
        }
        else if (response.d_status == REWRITE_DONE)
        {
#ifdef CVC4_ASSERTIONS
          RewriteResponse r2 =
              d_theoryRewriters[newTheoryId]->postRewrite(response.d_node);
          Assert(r2.d_node == response.d_node)
              << r2.d_node << " != " << response.d_node;
#endif
          rewriteStackTop.d_node = response.d_node;
          break;
        }
        // Check for trivial rewrite loops of size 1 or 2
        Assert(response.d_node != rewriteStackTop.d_node);
        Assert(d_theoryRewriters[rewriteStackTop.getTheoryId()]
                   ->postRewrite(response.d_node)
                   .d_node
               != rewriteStackTop.d_node);
        rewriteStackTop.d_node = response.d_node;
      }

      // We're done with the post rewrite, so we add to the cache
      setPostRewriteCache(rewriteStackTop.getOriginalTheoryId(),
                          rewriteStackTop.d_original,
                          rewriteStackTop.d_node);
    }
    else
    {
      // We were already in cache, so just remember it
      rewriteStackTop.d_node = cached;
      rewriteStackTop.d_theoryId = theoryOf(cached);
    }

    // If this is the last node, just return
    if (rewriteStack.size() == 1) {
      Assert(!isEquality || rewriteStackTop.d_node.getKind() == kind::EQUAL
             || rewriteStackTop.d_node.isConst());
      return rewriteStackTop.d_node;
    }

    // We're done with this node, append it to the parent
    rewriteStack[rewriteStack.size() - 2].d_builder << rewriteStackTop.d_node;
    rewriteStack.pop_back();
  }

  Unreachable();
} /* Rewriter::rewriteTo() */

RewriteResponse Rewriter::preRewrite(theory::TheoryId theoryId,
                                     TNode n,
                                     TConvProofGenerator* tcpg)
{
  Kind k = n.getKind();
  std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn =
      (k == kind::EQUAL) ? d_preRewritersEqual[theoryId] : d_preRewriters[k];
  if (fn == nullptr)
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
  return fn(&d_re, n);
}

RewriteResponse Rewriter::postRewrite(theory::TheoryId theoryId,
                                      TNode n,
                                      TConvProofGenerator* tcpg)
{
  Kind k = n.getKind();
  std::function<RewriteResponse(RewriteEnvironment*, TNode)> fn =
      (k == kind::EQUAL) ? d_postRewritersEqual[theoryId] : d_postRewriters[k];
  if (fn == nullptr)
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
  return fn(&d_re, n);
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
      Node tidn = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(theoryId);
      // add small step trusted rewrite
      NodeManager* nm = NodeManager::currentNM();
      tcpg->addRewriteStep(proven[0],
                           proven[1],
                           PfRule::THEORY_REWRITE,
                           {},
                           {proven, tidn, nm->mkConst(isPre)});
    }
    else
    {
      // store proven rewrite step
      tcpg->addRewriteStep(proven[0], proven[1], pg);
    }
  }
  return RewriteResponse(tresponse.d_status, trn.getNode());
}

void Rewriter::clearCaches() {
  Rewriter* rewriter = getInstance();

#ifdef CVC4_ASSERTIONS
  rewriter->d_rewriteStack.reset(nullptr);
#endif

  rewriter->clearCachesInternal();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
