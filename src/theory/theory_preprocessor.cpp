/*********************                                                        */
/*! \file theory_preprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory preprocessor
 **/

#include "theory/theory_preprocessor.h"

#include "expr/lazy_proof.h"
#include "expr/skolem_manager.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

using namespace std;

namespace CVC4 {
namespace theory {

TheoryPreprocessor::TheoryPreprocessor(TheoryEngine& engine,
                                       RemoveTermFormulas& tfr,
                                       ProofNodeManager* pnm)
    : d_engine(engine),
      d_logicInfo(engine.getLogicInfo()),
      d_ppCache(),
      d_tfr(tfr),
      d_pfContext(),
      d_tpg(pnm ? new TConvProofGenerator(pnm, &d_pfContext) : nullptr),
      d_lp(pnm ? new LazyCDProof(pnm, nullptr, &d_pfContext) : nullptr)
{
  if (isProofEnabled())
  {
    // enable proofs in the term formula remover
    if (pnm != nullptr)
    {
      d_tfr.setProofChecker(pnm->getChecker());
    }
    // push the proof context, since proof steps may be cleared on calls to
    // clearCache() below.
    d_pfContext.push();
  }
}

TheoryPreprocessor::~TheoryPreprocessor() {}

void TheoryPreprocessor::clearCache()
{
  d_ppCache.clear();
  // clear proofs from d_tpg and d_lp using internal push/pop context
  if (isProofEnabled())
  {
    d_pfContext.pop();
    d_pfContext.push();
  }
}

TrustNode TheoryPreprocessor::preprocess(TNode node,
                                         std::vector<TrustNode>& newLemmas,
                                         std::vector<Node>& newSkolems,
                                         bool doTheoryPreprocess)
{
  // In this method, all rewriting steps of node are stored in d_tpg.

  // Run theory preprocessing, maybe
  Node ppNode = node;
  if (doTheoryPreprocess)
  {
    // run theory preprocessing
    TrustNode tpp = theoryPreprocess(node);
    ppNode = tpp.getNode();
  }

  // Remove the ITEs
  Trace("te-tform-rm") << "Remove term formulas from " << ppNode << std::endl;
  TrustNode ttfr = d_tfr.run(ppNode, newLemmas, newSkolems, false);
  Trace("te-tform-rm") << "..done " << ttfr.getNode() << std::endl;
  Node retNode = ttfr.getNode();
  if (d_tpg != nullptr)
  {
    if (retNode != ppNode)
    {
      if (ttfr.getGenerator() != nullptr)
      {
        // store as a rewrite in d_tpg
        d_tpg->addRewriteStep(ppNode, retNode, ttfr.getGenerator());
      }
    }
  }

  if (Debug.isOn("lemma-ites"))
  {
    Debug("lemma-ites") << "removed ITEs from lemma: " << ttfr.getNode()
                        << endl;
    Debug("lemma-ites") << " + now have the following " << newLemmas.size()
                        << " lemma(s):" << endl;
    for (size_t i = 0, lsize = newLemmas.size(); i <= lsize; ++i)
    {
      Debug("lemma-ites") << " + " << newLemmas[i].getNode() << endl;
    }
    Debug("lemma-ites") << endl;
  }
  // Rewrite the main node, we rewrite and store the proof step, if necessary,
  // in d_tpg, which maintains the fact that d_tpg can prove the rewrite.
  retNode = rewriteWithProof(retNode);

  // now, rewrite the lemmas
  for (size_t i = 0, lsize = newLemmas.size(); i < lsize; ++i)
  {
    // get the trust node to process
    TrustNode trn = newLemmas[i];
    Assert(trn.getKind() == TrustNodeKind::LEMMA);
    Node assertion = trn.getNode();
    // rewrite, which is independent of d_tpg, since additional lemmas
    // are justified separately.
    Node rewritten = Rewriter::rewrite(assertion);
    if (assertion != rewritten)
    {
      if (trn.getGenerator() != nullptr)
      {
        Assert(d_lp != nullptr);
        // store in the lazy proof
        d_lp->addLazyStep(assertion, trn.getGenerator());
        d_lp->addStep(rewritten,
                      PfRule::MACRO_SR_PRED_TRANSFORM,
                      {assertion},
                      {rewritten});
        newLemmas[i] = TrustNode::mkTrustLemma(rewritten, d_lp.get());
      }
      else
      {
        // not tracking proofs, just make new
        newLemmas[i] = TrustNode::mkTrustLemma(rewritten, nullptr);
      }
    }
  }
  return TrustNode::mkTrustRewrite(node, retNode, d_tpg.get());
}

struct preprocess_stack_element
{
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode n) : node(n), children_added(false) {}
};

TrustNode TheoryPreprocessor::theoryPreprocess(TNode assertion)
{
  Trace("theory::preprocess")
      << "TheoryPreprocessor::theoryPreprocess(" << assertion << ")" << endl;
  // spendResource();

  // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    Debug("theory::internal")
        << "TheoryPreprocessor::theoryPreprocess(" << assertion
        << "): processing " << current << endl;

    // If node already in the cache we're done, pop from the stack
    NodeMap::iterator find = d_ppCache.find(current);
    if (find != d_ppCache.end())
    {
      toVisit.pop_back();
      continue;
    }

    if (!d_logicInfo.isTheoryEnabled(Theory::theoryOf(current))
        && Theory::theoryOf(current) != THEORY_SAT_SOLVER)
    {
      stringstream ss;
      ss << "The logic was specified as " << d_logicInfo.getLogicString()
         << ", which doesn't include " << Theory::theoryOf(current)
         << ", but got a preprocessing-time fact for that theory." << endl
         << "The fact:" << endl
         << current;
      throw LogicException(ss.str());
    }

    // If this is an atom, we preprocess its terms with the theory ppRewriter
    if (Theory::theoryOf(current) != THEORY_BOOL)
    {
      Node ppRewritten = ppTheoryRewrite(current);
      d_ppCache[current] = ppRewritten;
      Assert(Rewriter::rewrite(d_ppCache[current]) == d_ppCache[current]);
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added)
    {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(d_ppCache.find(current[i]) != d_ppCache.end());
        builder << d_ppCache[current[i]];
      }
      // Mark the substitution and continue
      Node result = builder;
      if (result != current)
      {
        result = Rewriter::rewrite(result);
      }
      Debug("theory::internal")
          << "TheoryPreprocessor::theoryPreprocess(" << assertion
          << "): setting " << current << " -> " << result << endl;
      d_ppCache[current] = result;
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.children_added = true;
        // We need to add the children
        for (TNode::iterator child_it = current.begin();
             child_it != current.end();
             ++child_it)
        {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_ppCache.find(childNode);
          if (childFind == d_ppCache.end())
          {
            toVisit.push_back(childNode);
          }
        }
      }
      else
      {
        // No children, so we're done
        Debug("substitution::internal")
            << "SubstitutionMap::internalSubstitute(" << assertion
            << "): setting " << current << " -> " << current << endl;
        d_ppCache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  // Return the substituted version
  Node res = d_ppCache[assertion];
  return TrustNode::mkTrustRewrite(assertion, res, d_tpg.get());
}

// Recursively traverse a term and call the theory rewriter on its sub-terms
Node TheoryPreprocessor::ppTheoryRewrite(TNode term)
{
  NodeMap::iterator find = d_ppCache.find(term);
  if (find != d_ppCache.end())
  {
    return (*find).second;
  }
  unsigned nc = term.getNumChildren();
  if (nc == 0)
  {
    return preprocessWithProof(term);
  }
  Trace("theory-pp") << "ppTheoryRewrite { " << term << endl;

  Node newTerm = term;
  // do not rewrite inside quantifiers
  if (!term.isClosure())
  {
    NodeBuilder<> newNode(term.getKind());
    if (term.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      newNode << term.getOperator();
    }
    unsigned i;
    for (i = 0; i < nc; ++i)
    {
      newNode << ppTheoryRewrite(term[i]);
    }
    newTerm = Node(newNode);
  }
  newTerm = rewriteWithProof(newTerm);
  newTerm = preprocessWithProof(newTerm);
  d_ppCache[term] = newTerm;
  Trace("theory-pp") << "ppTheoryRewrite returning " << newTerm << "}" << endl;
  return newTerm;
}

Node TheoryPreprocessor::rewriteWithProof(Node term)
{
  Node termr = Rewriter::rewrite(term);
  // store rewrite step if tracking proofs and it rewrites
  if (isProofEnabled())
  {
    // may rewrite the same term more than once, thus check hasRewriteStep
    if (termr != term)
    {
      if (d_tpg->hasRewriteStep(term))
      {
        // should match
        Assert(d_tpg->getRewriteStep(term) == termr);
      }
      else
      {
        d_tpg->addRewriteStep(term, termr, PfRule::REWRITE, {}, {term});
      }
    }
  }
  return termr;
}

Node TheoryPreprocessor::preprocessWithProof(Node term)
{
  // important that it is in rewritten form, to ensure that the rewrite steps
  // recorded in d_tpg are functional.
  Assert(term == Rewriter::rewrite(term));
  // call ppRewrite for the given theory
  TrustNode trn = d_engine.theoryOf(term)->ppRewrite(term);
  if (trn.isNull())
  {
    // no change, return original term
    return term;
  }
  Node termr = trn.getNode();
  Assert(term != termr);
  if (isProofEnabled())
  {
    if (trn.getGenerator() != nullptr)
    {
      d_tpg->addRewriteStep(term, termr, trn.getGenerator());
    }
    else
    {
      // small step trust
      d_tpg->addRewriteStep(
          term, termr, PfRule::THEORY_PREPROCESS, {}, {term.eqNode(termr)});
    }
  }
  termr = rewriteWithProof(termr);
  return ppTheoryRewrite(termr);
}

bool TheoryPreprocessor::isProofEnabled() const { return d_tpg != nullptr; }

}  // namespace theory
}  // namespace CVC4
