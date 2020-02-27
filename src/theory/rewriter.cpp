/*********************                                                        */
/*! \file rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Liana Hadarean, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
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
      : node(node),
        original(node),
        theoryId(theoryId),
        originalTheoryId(theoryId),
        nextChild(0)
  {
  }

  TheoryId getTheoryId() { return static_cast<TheoryId>(theoryId); }

  TheoryId getOriginalTheoryId()
  {
    return static_cast<TheoryId>(originalTheoryId);
  }

  /** The node we're currently rewriting */
  Node node;
  /** Original node */
  Node original;
  /** Id of the theory that's currently rewriting this node */
  unsigned theoryId         : 8;
  /** Id of the original theory that started the rewrite */
  unsigned originalTheoryId : 8;
  /** Index of the child this node is done rewriting */
  unsigned nextChild        : 32;
  /** Builder for this node */
  NodeBuilder<> builder;
};

Node Rewriter::rewrite(TNode node) {
  if (node.getNumChildren() == 0)
  {
    // Nodes with zero children should never change via rewriting. We return
    // eagerly for the sake of efficiency here.
    return node;
  }
  Rewriter& rewriter = getInstance();
  return rewriter.rewriteTo(theoryOf(node), node);
}

Rewriter& Rewriter::getInstance()
{
  thread_local static Rewriter rewriter;
  return rewriter;
}

Node Rewriter::rewriteTo(theory::TheoryId theoryId, Node node) {

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
  if (!cached.isNull()) {
    return cached;
  }

  // Put the node on the stack in order to start the "recursive" rewrite
  vector<RewriteStackElement> rewriteStack;
  rewriteStack.push_back(RewriteStackElement(node, theoryId));

  ResourceManager* rm = NULL;
  bool hasSmtEngine = smt::smtEngineInScope();
  if (hasSmtEngine) {
    rm = NodeManager::currentResourceManager();
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
                      << rewriteStackTop.node << std::endl;

    // Before rewriting children we need to do a pre-rewrite of the node
    if (rewriteStackTop.nextChild == 0) {

      // Check if the pre-rewrite has already been done (it's in the cache)
      Node cached = getPreRewriteCache(rewriteStackTop.getTheoryId(),
                                       rewriteStackTop.node);
      if (cached.isNull()) {
        // Rewrite until fix-point is reached
        for(;;) {
          // Perform the pre-rewrite
          RewriteResponse response =
              d_theoryRewriters[rewriteStackTop.getTheoryId()]->preRewrite(
                  rewriteStackTop.node);
          // Put the rewritten node to the top of the stack
          rewriteStackTop.node = response.d_node;
          TheoryId newTheory = theoryOf(rewriteStackTop.node);
          // In the pre-rewrite, if changing theories, we just call the other theories pre-rewrite
          if (newTheory == rewriteStackTop.getTheoryId()
              && response.d_status == REWRITE_DONE)
          {
            break;
          }
          rewriteStackTop.theoryId = newTheory;
        }
        // Cache the rewrite
        setPreRewriteCache(rewriteStackTop.getOriginalTheoryId(),
                           rewriteStackTop.original,
                           rewriteStackTop.node);
      }
      // Otherwise we're have already been pre-rewritten (in pre-rewrite cache)
      else {
        // Continue with the cached version
        rewriteStackTop.node = cached;
        rewriteStackTop.theoryId = theoryOf(cached);
      }
    }

    rewriteStackTop.original =rewriteStackTop.node;
    // Now it's time to rewrite the children, check if this has already been done
    Node cached = getPostRewriteCache(rewriteStackTop.getTheoryId(),
                                      rewriteStackTop.node);
    // If not, go through the children
    if(cached.isNull()) {

      // The child we need to rewrite
      unsigned child = rewriteStackTop.nextChild++;

      // To build the rewritten expression we set up the builder
      if(child == 0) {
        if (rewriteStackTop.node.getNumChildren() > 0) {
          // The children will add themselves to the builder once they're done
          rewriteStackTop.builder << rewriteStackTop.node.getKind();
          kind::MetaKind metaKind = rewriteStackTop.node.getMetaKind();
          if (metaKind == kind::metakind::PARAMETERIZED) {
            rewriteStackTop.builder << rewriteStackTop.node.getOperator();
          }
        }
      }

      // Process the next child
      if(child < rewriteStackTop.node.getNumChildren()) {
        // The child node
        Node childNode = rewriteStackTop.node[child];
        // Push the rewrite request to the stack (NOTE: rewriteStackTop might be a bad reference now)
        rewriteStack.push_back(RewriteStackElement(childNode, theoryOf(childNode)));
        // Go on with the rewriting
        continue;
      }

      // Incorporate the children if necessary
      if (rewriteStackTop.node.getNumChildren() > 0) {
        Node rewritten = rewriteStackTop.builder;
        rewriteStackTop.node = rewritten;
        rewriteStackTop.theoryId = theoryOf(rewriteStackTop.node);
      }

      // Done with all pre-rewriting, so let's do the post rewrite
      for(;;) {
        // Do the post-rewrite
        RewriteResponse response =
            d_theoryRewriters[rewriteStackTop.getTheoryId()]->postRewrite(
                rewriteStackTop.node);
        // We continue with the response we got
        TheoryId newTheoryId = theoryOf(response.d_node);
        if (newTheoryId != rewriteStackTop.getTheoryId()
            || response.d_status == REWRITE_AGAIN_FULL)
        {
          // In the post rewrite if we've changed theories, we must do a full rewrite
          Assert(response.d_node != rewriteStackTop.node);
          //TODO: this is not thread-safe - should make this assertion dependent on sequential build
#ifdef CVC4_ASSERTIONS
          Assert(d_rewriteStack->find(response.d_node)
                 == d_rewriteStack->end());
          d_rewriteStack->insert(response.d_node);
#endif
          Node rewritten = rewriteTo(newTheoryId, response.d_node);
          rewriteStackTop.node = rewritten;
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
          Assert(r2.d_node == response.d_node);
#endif
          rewriteStackTop.node = response.d_node;
          break;
        }
        // Check for trivial rewrite loops of size 1 or 2
        Assert(response.d_node != rewriteStackTop.node);
        Assert(d_theoryRewriters[rewriteStackTop.getTheoryId()]
                   ->postRewrite(response.d_node)
                   .d_node
               != rewriteStackTop.node);
        rewriteStackTop.node = response.d_node;
      }
      // We're done with the post rewrite, so we add to the cache
      setPostRewriteCache(rewriteStackTop.getOriginalTheoryId(),
                          rewriteStackTop.original,
                          rewriteStackTop.node);
    } else {
      // We were already in cache, so just remember it
      rewriteStackTop.node = cached;
      rewriteStackTop.theoryId = theoryOf(cached);
    }

    // If this is the last node, just return
    if (rewriteStack.size() == 1) {
      Assert(!isEquality || rewriteStackTop.node.getKind() == kind::EQUAL
             || rewriteStackTop.node.isConst());
      return rewriteStackTop.node;
    }

    // We're done with this node, append it to the parent
    rewriteStack[rewriteStack.size() - 2].builder << rewriteStackTop.node;
    rewriteStack.pop_back();
  }

  Unreachable();
}/* Rewriter::rewriteTo() */

void Rewriter::clearCaches() {
  Rewriter& rewriter = getInstance();

#ifdef CVC4_ASSERTIONS
  rewriter.d_rewriteStack.reset(nullptr);
#endif

  rewriter.clearCachesInternal();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
