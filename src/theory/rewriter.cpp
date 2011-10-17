/*********************                                                        */
/*! \file rewriter.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/theory.h"
#include "theory/rewriter.h"
#include "theory/rewriter_tables.h"

using namespace std;

namespace CVC4 {
namespace theory {

/**
 * TheoryEngine::rewrite() keeps a stack of things that are being pre-
 * and post-rewritten.  Each element of the stack is a
 * RewriteStackElement.
 */
struct RewriteStackElement {

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

  /**
   * Construct a fresh stack element.
   */
  RewriteStackElement(Node node, TheoryId theoryId) :
    node(node),
    original(node),
    theoryId(theoryId),
    originalTheoryId(theoryId),
    nextChild(0) {
  }
};

Node Rewriter::rewrite(Node node) {
  return rewriteTo(theory::Theory::theoryOf(node), node);
}

Node Rewriter::rewriteEquality(theory::TheoryId theoryId, TNode node) {
  Trace("rewriter") << "Rewriter::rewriteEquality(" << theoryId << "," << node << ")"<< std::endl;
  return Rewriter::callRewriteEquality(theoryId, node);
}

Node Rewriter::rewriteTo(theory::TheoryId theoryId, Node node) {

  Trace("rewriter") << "Rewriter::rewriteTo(" << theoryId << "," << node << ")"<< std::endl;

  // Put the node on the stack in order to start the "recursive" rewrite
  vector<RewriteStackElement> rewriteStack;
  rewriteStack.push_back(RewriteStackElement(node, theoryId));

  // Rewrite until the stack is empty
  for (;;){

    // Get the top of the recursion stack
    RewriteStackElement& rewriteStackTop = rewriteStack.back();

    Trace("rewriter") << "Rewriter::rewriting: " << (TheoryId) rewriteStackTop.theoryId << "," << rewriteStackTop.node << std::endl;

    // Before rewriting children we need to do a pre-rewrite of the node
    if (rewriteStackTop.nextChild == 0) {

      // Check if the pre-rewrite has already been done (it's in the cache)
      Node cached = Rewriter::getPreRewriteCache((TheoryId) rewriteStackTop.theoryId, rewriteStackTop.node);
      if (cached.isNull()) {
        // Rewrite until fix-point is reached
        for(;;) {
          // Perform the pre-rewrite
          RewriteResponse response = Rewriter::callPreRewrite((TheoryId) rewriteStackTop.theoryId, rewriteStackTop.node);
          // Put the rewritten node to the top of the stack
          rewriteStackTop.node = response.node;
          TheoryId newTheory = Theory::theoryOf(rewriteStackTop.node);
          // In the pre-rewrite, if changing theories, we just call the other theories pre-rewrite
          if (newTheory == (TheoryId) rewriteStackTop.theoryId && response.status == REWRITE_DONE) {
            break;
          }
          rewriteStackTop.theoryId = newTheory;
        }
        // Cache the rewrite
        Rewriter::setPreRewriteCache((TheoryId) rewriteStackTop.originalTheoryId, rewriteStackTop.original, rewriteStackTop.node);
      }
      // Otherwise we're have already been pre-rewritten (in pre-rewrite cache)
      else {
        // Continue with the cached version
        rewriteStackTop.node = cached;
        rewriteStackTop.theoryId = Theory::theoryOf(cached);
      }
    }

    // Now it's time to rewrite the children, check if this has already been done
    Node cached = Rewriter::getPostRewriteCache((TheoryId) rewriteStackTop.theoryId, rewriteStackTop.node);
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
        rewriteStack.push_back(RewriteStackElement(childNode, Theory::theoryOf(childNode)));
        // Go on with the rewriting
        continue;
      }

      // Incorporate the children if necessary
      if (rewriteStackTop.node.getNumChildren() > 0) {
        rewriteStackTop.node = rewriteStackTop.builder;
        rewriteStackTop.theoryId = Theory::theoryOf(rewriteStackTop.node);
      }

      // Done with all pre-rewriting, so let's do the post rewrite
      for(;;) {
        // Do the post-rewrite
        RewriteResponse response = Rewriter::callPostRewrite((TheoryId) rewriteStackTop.theoryId, rewriteStackTop.node);
        // We continue with the response we got
        rewriteStackTop.node = response.node;
        TheoryId newTheoryId = Theory::theoryOf(rewriteStackTop.node);
        if (newTheoryId != (TheoryId) rewriteStackTop.theoryId || response.status == REWRITE_AGAIN_FULL) {
          // In the post rewrite if we've changed theories, we must do a full rewrite
          rewriteStackTop.node = rewriteTo(newTheoryId, rewriteStackTop.node);
          break;
        } else if (response.status == REWRITE_DONE) {
          break;
        }
      }
      // We're done with the post rewrite, so we add to the cache
      Rewriter::setPostRewriteCache((TheoryId) rewriteStackTop.originalTheoryId, rewriteStackTop.original, rewriteStackTop.node);

    } else {
      // We were already in cache, so just remember it
      rewriteStackTop.node = cached;
      rewriteStackTop.theoryId = Theory::theoryOf(cached);
    }

    // If this is the last node, just return
    if (rewriteStack.size() == 1) {
      return rewriteStackTop.node;
    }

    // We're done with this node, append it to the parent
    rewriteStack[rewriteStack.size() - 2].builder << rewriteStackTop.node;
    rewriteStack.pop_back();
  }

  Unreachable();
  return Node::null();
}


}
}
