/*********************                                                        */
/*! \file theory_preprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
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
                                       context::UserContext* userContext,
                                       ProofNodeManager* pnm)
    : d_engine(engine),
      d_logicInfo(engine.getLogicInfo()),
      d_ppCache(userContext),
      d_tfr(userContext, pnm),
      d_tpg(pnm ? new TConvProofGenerator(
                      pnm,
                      userContext,
                      TConvPolicy::FIXPOINT,
                      TConvCachePolicy::NEVER,
                      "TheoryPreprocessor::preprocess_rewrite",
                      &d_iqtc)
                : nullptr),
      d_tspg(nullptr),
      d_tpgRew(pnm ? new TConvProofGenerator(pnm,
                                             userContext,
                                             TConvPolicy::FIXPOINT,
                                             TConvCachePolicy::NEVER,
                                             "TheoryPreprocessor::rewrite")
                   : nullptr),
      d_tspgNoPp(nullptr),
      d_lp(pnm ? new LazyCDProof(pnm,
                                 nullptr,
                                 userContext,
                                 "TheoryPreprocessor::LazyCDProof")
               : nullptr)
{
  if (isProofEnabled())
  {
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
        pnm, ts, userContext, "TheoryPreprocessor::sequence"));
    // Make the "no preprocess" term conversion sequence generator, which
    // applies only steps (2) and (3), where notice (3) must use the
    // "pure rewrite" term conversion (d_tpgRew).
    std::vector<ProofGenerator*> tsNoPp;
    tsNoPp.push_back(d_tfr.getTConvProofGenerator());
    tsNoPp.push_back(d_tpgRew.get());
    d_tspgNoPp.reset(new TConvSeqProofGenerator(
        pnm, tsNoPp, userContext, "TheoryPreprocessor::sequence_no_pp"));
  }
}

TheoryPreprocessor::~TheoryPreprocessor() {}

TrustNode TheoryPreprocessor::preprocess(TNode node,
                                         std::vector<TrustNode>& newLemmas,
                                         std::vector<Node>& newSkolems,
                                         bool doTheoryPreprocess)
{
  // In this method, all rewriting steps of node are stored in d_tpg.

  Trace("tpp-debug") << "TheoryPreprocessor::preprocess: start " << node
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

  // Remove the ITEs
  TrustNode ttfr = d_tfr.run(ppNode, newLemmas, newSkolems);
  Node rtfNode = ttfr.getNode();

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

  if (Trace.isOn("tpp-debug"))
  {
    if (node != ppNode)
    {
      Trace("tpp-debug") << "after preprocessing : " << ppNode << std::endl;
    }
    if (rtfNode != ppNode)
    {
      Trace("tpp-debug") << "after rtf : " << rtfNode << std::endl;
    }
    if (retNode != rtfNode)
    {
      Trace("tpp-debug") << "after rewriting : " << retNode << std::endl;
    }
    Trace("tpp-debug") << "TheoryPreprocessor::preprocess: finish" << std::endl;
  }
  if (node == retNode)
  {
    Trace("tpp-debug") << "...TheoryPreprocessor::preprocess returned no change"
                       << std::endl;
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
    tret.debugCheckClosed("tpp-debug", "TheoryPreprocessor::lemma_ret");
  }
  else
  {
    tret = TrustNode::mkTrustRewrite(node, retNode, nullptr);
  }

  // now, rewrite the lemmas
  Trace("tpp-debug") << "TheoryPreprocessor::preprocess: process lemmas"
                     << std::endl;
  for (size_t i = 0, lsize = newLemmas.size(); i < lsize; ++i)
  {
    // get the trust node to process
    TrustNode trn = newLemmas[i];
    trn.debugCheckClosed(
        "tpp-debug", "TheoryPreprocessor::lemma_new_initial", false);
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
                          PfRule::THEORY_PREPROCESS_LEMMA,
                          true,
                          "TheoryPreprocessor::rewrite_lemma_new");
        d_lp->addStep(rewritten,
                      PfRule::MACRO_SR_PRED_TRANSFORM,
                      {assertion},
                      {rewritten});
      }
      newLemmas[i] = TrustNode::mkTrustLemma(rewritten, d_lp.get());
    }
    Assert(!isProofEnabled() || newLemmas[i].getGenerator() != nullptr);
    newLemmas[i].debugCheckClosed("tpp-debug", "TheoryPreprocessor::lemma_new");
  }
  Trace("tpp-debug") << "...TheoryPreprocessor::preprocess returned "
                     << tret.getNode() << std::endl;
  return tret;
}

TrustNode TheoryPreprocessor::preprocessLemma(TrustNode node,
                                              std::vector<TrustNode>& newLemmas,
                                              std::vector<Node>& newSkolems,
                                              bool doTheoryPreprocess)
{
  // what was originally proven
  Node lemma = node.getProven();
  TrustNode tplemma =
      preprocess(lemma, newLemmas, newSkolems, doTheoryPreprocess);
  if (tplemma.isNull())
  {
    // no change needed
    return node;
  }
  Assert(tplemma.getKind() == TrustNodeKind::REWRITE);
  // what it was preprocessed to
  Node lemmap = tplemma.getNode();
  Assert(lemmap != node.getProven());
  // process the preprocessing
  if (isProofEnabled())
  {
    Assert(d_lp != nullptr);
    // add the original proof to the lazy proof
    d_lp->addLazyStep(node.getProven(), node.getGenerator());
    // only need to do anything if lemmap changed in a non-trivial way
    if (!CDProof::isSame(lemmap, lemma))
    {
      d_lp->addLazyStep(tplemma.getProven(),
                        tplemma.getGenerator(),
                        PfRule::PREPROCESS_LEMMA,
                        true,
                        "TheoryEngine::lemma_pp");
      // ---------- from node -------------- from theory preprocess
      // lemma                lemma = lemmap
      // ------------------------------------------ EQ_RESOLVE
      // lemmap
      std::vector<Node> pfChildren;
      pfChildren.push_back(lemma);
      pfChildren.push_back(tplemma.getProven());
      d_lp->addStep(lemmap, PfRule::EQ_RESOLVE, pfChildren, {});
    }
  }
  return TrustNode::mkTrustLemma(lemmap, d_lp.get());
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
      Assert(Rewriter::rewrite(d_ppCache[current].get())
             == d_ppCache[current].get());
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
        builder << d_ppCache[current[i]].get();
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
  if (term.getNumChildren() == 0)
  {
    return preprocessWithProof(term);
  }
  Trace("theory-pp") << "ppTheoryRewrite { " << term << endl;
  // We must rewrite before preprocessing, because some terms when rewritten
  // may introduce new terms that are not top-level and require preprocessing.
  // An example of this is (forall ((x Int)) (and (tail L) (P x))) which
  // rewrites to (and (tail L) (forall ((x Int)) (P x))). The subterm (tail L)
  // must be preprocessed as a child here.
  Node newTerm = rewriteWithProof(term);
  // do not rewrite inside quantifiers
  if (newTerm.getNumChildren() > 0 && !newTerm.isClosure())
  {
    NodeBuilder<> newNode(newTerm.getKind());
    if (newTerm.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      newNode << newTerm.getOperator();
    }
    for (const Node& nt : newTerm)
    {
      newNode << ppTheoryRewrite(nt);
    }
    newTerm = Node(newNode);
    newTerm = rewriteWithProof(newTerm);
  }
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
      Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (rewriting) "
                         << term << " -> " << termr << std::endl;
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
      Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (generator) "
                         << term << " -> " << termr << std::endl;
      trn.debugCheckClosed("tpp-debug",
                           "TheoryPreprocessor::preprocessWithProof");
      // always use term context hash 0 (default)
      d_tpg->addRewriteStep(
          term, termr, trn.getGenerator(), PfRule::ASSUME, true);
    }
    else
    {
      Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (trusted) "
                         << term << " -> " << termr << std::endl;
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
