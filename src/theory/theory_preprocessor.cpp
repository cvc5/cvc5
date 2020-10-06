/*********************                                                        */
/*! \file theory_preprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
      d_tpg(pnm ? new TConvProofGenerator(
                      pnm,
                      &d_pfContext,
                      TConvPolicy::FIXPOINT,
                      TConvCachePolicy::NEVER,
                      "TheoryPreprocessor::preprocess_rewrite",
                      &d_iqtc)
                : nullptr),
      d_tspg(nullptr),
      d_tpgRew(pnm ? new TConvProofGenerator(pnm,
                                             &d_pfContext,
                                             TConvPolicy::FIXPOINT,
                                             TConvCachePolicy::NEVER,
                                             "TheoryPreprocessor::rewrite")
                   : nullptr),
      d_tspgNoPp(nullptr),
      d_lp(pnm ? new LazyCDProof(pnm,
                                 nullptr,
                                 &d_pfContext,
                                 "TheoryPreprocessor::LazyCDProof")
               : nullptr)
{
  if (isProofEnabled())
  {
    // push the proof context, since proof steps may be cleared on calls to
    // clearCache() below.
    d_pfContext.push();
    // Make the main term conversion sequence generator, which tracks up to
    // three conversions made in succession:
    // (1) theory preprocessing+rewriting
    // (2) term formula removal
    // (3) rewriting
    // Steps (1) and (3) use a common term conversion generator.
    std::vector<ProofGenerator*> ts;
    ts.push_back(d_tpg.get());
    ts.push_back(d_tfr.getTConvProofGenerator());
    ts.push_back(d_tpg.get());
    d_tspg.reset(new TConvSeqProofGenerator(
        pnm, ts, &d_pfContext, "TheoryPreprocessor::sequence"));
    // Make the "no preprocess" term conversion sequence generator, which
    // applies only steps (2) and (3), where notice (3) must use the
    // "pure rewrite" term conversion (d_tpgRew).
    std::vector<ProofGenerator*> tsNoPp;
    tsNoPp.push_back(d_tfr.getTConvProofGenerator());
    tsNoPp.push_back(d_tpgRew.get());
    d_tspgNoPp.reset(new TConvSeqProofGenerator(
        pnm, tsNoPp, &d_pfContext, "TheoryPreprocessor::sequence_no_pp"));
  }
}

TheoryPreprocessor::~TheoryPreprocessor() {}

void TheoryPreprocessor::clearCache()
{
  Trace("tpp-proof-debug") << "TheoryPreprocessor::clearCache" << std::endl;
  d_ppCache.clear();
  // clear proofs from d_tpg, d_tspg and d_lp using internal push/pop context
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

  Trace("tpp-proof-debug") << "TheoryPreprocessor::preprocess: start " << node
                           << ", doTheoryPreprocess=" << doTheoryPreprocess
                           << std::endl;
  // Run theory preprocessing, maybe
  Node ppNode = node;
  if (doTheoryPreprocess)
  {
    // run theory preprocessing
    TrustNode tpp = theoryPreprocess(node);
    ppNode = tpp.getNode();
  }
  Trace("tpp-proof-debug")
      << "TheoryPreprocessor::preprocess: after preprocessing " << ppNode
      << std::endl;

  // Remove the ITEs
  Trace("te-tform-rm") << "Remove term formulas from " << ppNode << std::endl;
  TrustNode ttfr = d_tfr.run(ppNode, newLemmas, newSkolems, false);
  Trace("te-tform-rm") << "..done " << ttfr.getNode() << std::endl;
  Node rtfNode = ttfr.getNode();
  Trace("tpp-proof-debug")
      << "TheoryPreprocessor::preprocess: rtf returned node " << rtfNode
      << std::endl;

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
  Node retNode = rewriteWithProof(rtfNode);
  Trace("tpp-proof-debug")
      << "TheoryPreprocessor::preprocess: after rewriting is " << retNode
      << std::endl;
  if (node == retNode)
  {
    // no change
    Assert(newLemmas.empty());
    return TrustNode::null();
  }

  // Now, sequence the conversion steps if proofs are enabled.
  TrustNode tret;
  if (isProofEnabled())
  {
    std::vector<Node> cterms;
    cterms.push_back(node);
    if (doTheoryPreprocess)
    {
      cterms.push_back(ppNode);
    }
    cterms.push_back(rtfNode);
    cterms.push_back(retNode);
    // We have that:
    // node -> ppNode via preprocessing + rewriting (if doTheoryPreprocess)
    // ppNode -> rtfNode via term formula removal
    // rtfNode -> retNode via rewriting
    if (!doTheoryPreprocess)
    {
      // If preprocessing is not performed, we cannot use the main sequence
      // generator, instead we use d_tspgNoPp.
      // We register the top-level rewrite in the pure rewrite term converter.
      d_tpgRew->addRewriteStep(
          rtfNode, retNode, PfRule::REWRITE, {}, {rtfNode});
      // Now get the trust node from the sequence generator
      tret = d_tspgNoPp->mkTrustRewriteSequence(cterms);
    }
    else
    {
      // we wil use the sequence generator
      tret = d_tspg->mkTrustRewriteSequence(cterms);
    }
    tret.debugCheckClosed("tpp-proof-debug", "TheoryPreprocessor::lemma_ret");
  }
  else
  {
    tret = TrustNode::mkTrustRewrite(node, retNode, nullptr);
  }

  // now, rewrite the lemmas
  Trace("tpp-proof-debug") << "TheoryPreprocessor::preprocess: process lemmas"
                           << std::endl;
  for (size_t i = 0, lsize = newLemmas.size(); i < lsize; ++i)
  {
    // get the trust node to process
    TrustNode trn = newLemmas[i];
    trn.debugCheckClosed(
        "tpp-proof-debug", "TheoryPreprocessor::lemma_new_initial", false);
    Assert(trn.getKind() == TrustNodeKind::LEMMA);
    Node assertion = trn.getNode();
    // rewrite, which is independent of d_tpg, since additional lemmas
    // are justified separately.
    Node rewritten = Rewriter::rewrite(assertion);
    if (assertion != rewritten)
    {
      if (isProofEnabled())
      {
        Assert(d_lp != nullptr);
        // store in the lazy proof
        d_lp->addLazyStep(assertion,
                          trn.getGenerator(),
                          true,
                          "TheoryPreprocessor::rewrite_lemma_new",
                          false,
                          PfRule::THEORY_PREPROCESS_LEMMA);
        d_lp->addStep(rewritten,
                      PfRule::MACRO_SR_PRED_TRANSFORM,
                      {assertion},
                      {rewritten});
      }
      newLemmas[i] = TrustNode::mkTrustLemma(rewritten, d_lp.get());
    }
    Assert(!isProofEnabled() || newLemmas[i].getGenerator() != nullptr);
    newLemmas[i].debugCheckClosed("tpp-proof-debug",
                                  "TheoryPreprocessor::lemma_new");
  }
  Trace("tpp-proof-debug") << "Preprocessed: " << node << " " << retNode
                           << std::endl;
  return tret;
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

    Trace("theory::preprocess-debug")
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
        result = rewriteWithProof(result);
      }
      Trace("theory::preprocess-debug")
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
        Trace("theory::preprocess-debug")
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
      Trace("tpp-proof-debug")
          << "TheoryPreprocessor: addRewriteStep (rewriting) " << term << " -> "
          << termr << std::endl;
      // always use term context hash 0 (default)
      d_tpg->addRewriteStep(term, termr, PfRule::REWRITE, {}, {term});
    }
  }
  return termr;
}

Node TheoryPreprocessor::preprocessWithProof(Node term)
{
  // Important that it is in rewritten form, to ensure that the rewrite steps
  // recorded in d_tpg are functional. In other words, there should not
  // be steps from the same term to multiple rewritten forms, which would be
  // the case if we registered a preprocessing step for a non-rewritten term.
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
      Trace("tpp-proof-debug")
          << "TheoryPreprocessor: addRewriteStep (generator) " << term << " -> "
          << termr << std::endl;
      trn.debugCheckClosed("tpp-proof-debug",
                           "TheoryPreprocessor::preprocessWithProof");
      // always use term context hash 0 (default)
      d_tpg->addRewriteStep(term, termr, trn.getGenerator());
    }
    else
    {
      Trace("tpp-proof-debug")
          << "TheoryPreprocessor: addRewriteStep (trusted) " << term << " -> "
          << termr << std::endl;
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
