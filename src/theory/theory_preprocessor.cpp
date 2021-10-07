/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory preprocessor.
 */

#include "theory/theory_preprocessor.h"

#include "expr/skolem_manager.h"
#include "proof/lazy_proof.h"
#include "smt/logic_exception.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "expr/term_context_stack.h"

using namespace std;

namespace cvc5 {
namespace theory {

TheoryPreprocessor::TheoryPreprocessor(Env& env, TheoryEngine& engine)
    : EnvObj(env),
      d_engine(engine),
      d_tfCache(userContext()),
      d_tfr(env),
      d_tpg(nullptr),
      d_tpgRtf(nullptr),
      d_tpgRew(nullptr),
      d_tspg(nullptr),
      d_lp(nullptr)
{
  // proofs are enabled in the theory preprocessor regardless of the proof mode
  ProofNodeManager* pnm = env.getProofNodeManager();
  if (pnm != nullptr)
  {
    context::Context* u = userContext();
    d_tpg.reset(
        new TConvProofGenerator(pnm,
                                u,
                                TConvPolicy::FIXPOINT,
                                TConvCachePolicy::NEVER,
                                "TheoryPreprocessor::preprocess_rewrite",
                                &d_iqtc));
    d_tpgRtf.reset(new TConvProofGenerator(pnm,
                                           u,
                                           TConvPolicy::FIXPOINT,
                                           TConvCachePolicy::NEVER,
                                           "TheoryPreprocessor::rtf",
                                           &d_iqtc));
    d_tpgRew.reset(new TConvProofGenerator(pnm,
                                           u,
                                           TConvPolicy::ONCE,
                                           TConvCachePolicy::NEVER,
                                           "TheoryPreprocessor::pprew"));
    d_lp.reset(
        new LazyCDProof(pnm, nullptr, u, "TheoryPreprocessor::LazyCDProof"));
    // Make the main term conversion sequence generator, which tracks up to
    // three conversions made in succession:
    // (1) rewriting
    // (2) (theory preprocessing+rewriting until fixed point)+term formula
    // removal+rewriting.
    std::vector<ProofGenerator*> ts;
    ts.push_back(d_tpgRew.get());
    ts.push_back(d_tpgRtf.get());
    d_tspg.reset(new TConvSeqProofGenerator(
        pnm, ts, userContext(), "TheoryPreprocessor::sequence"));
  }
}

TheoryPreprocessor::~TheoryPreprocessor() {}

TrustNode TheoryPreprocessor::preprocess(TNode node,
                                         std::vector<SkolemLemma>& newLemmas)
{
  return preprocessInternal(node, newLemmas, true);
}

TrustNode TheoryPreprocessor::preprocessInternal(
    TNode node, std::vector<SkolemLemma>& newLemmas, bool procLemmas)
{
  // In this method, all rewriting steps of node are stored in d_tpg.

  Trace("tpp") << "TheoryPreprocessor::preprocess: start " << node << std::endl;

  // We must rewrite before preprocessing, because some terms when rewritten
  // may introduce new terms that are not top-level and require preprocessing.
  // An example of this is (forall ((x Int)) (and (tail L) (P x))) which
  // rewrites to (and (tail L) (forall ((x Int)) (P x))). The subterm (tail L)
  // must be preprocessed as a child here.
  Node irNode = rewriteWithProof(node, d_tpgRew.get(), true);

  // run theory preprocessing
  TrustNode tpp = theoryPreprocess(irNode, newLemmas);
  Node ppNode = tpp.getNode();

  if (Trace.isOn("tpp-debug"))
  {
    if (node != irNode)
    {
      Trace("tpp-debug") << "after initial rewriting : " << irNode << std::endl;
    }
    if (irNode != ppNode)
    {
      Trace("tpp-debug")
          << "after preprocessing + rewriting and term formula removal : "
          << ppNode << std::endl;
    }
    Trace("tpp-debug") << "TheoryPreprocessor::preprocess: finish" << std::endl;
  }

  if (procLemmas)
  {
    // Also must preprocess the new lemmas. This is especially important for
    // formulas containing witness terms whose bodies are not in preprocessed
    // form, as term formula removal introduces new lemmas for these that
    // require theory-preprocessing.
    size_t i = 0;
    while (i < newLemmas.size())
    {
      TrustNode cur = newLemmas[i].d_lemma;
      newLemmas[i].d_lemma = preprocessLemmaInternal(cur, newLemmas, false);
      Trace("tpp") << "Final lemma : " << newLemmas[i].getProven() << std::endl;
      i++;
    }
  }

  if (node == ppNode)
  {
    Trace("tpp-debug") << "...TheoryPreprocessor::preprocess returned no change"
                       << std::endl;
    // no change
    return TrustNode::null();
  }

  // Now, sequence the conversion steps if proofs are enabled.
  TrustNode tret;
  if (isProofEnabled())
  {
    std::vector<Node> cterms;
    cterms.push_back(node);
    cterms.push_back(irNode);
    cterms.push_back(ppNode);
    // We have that:
    // node -> irNode via rewriting
    // irNode -> ppNode via theory-preprocessing + rewriting + tf removal
    tret = d_tspg->mkTrustRewriteSequence(cterms);
    tret.debugCheckClosed("tpp-debug", "TheoryPreprocessor::lemma_ret");
  }
  else
  {
    tret = TrustNode::mkTrustRewrite(node, ppNode, nullptr);
  }

  Trace("tpp-debug") << "...TheoryPreprocessor::preprocess returned "
                     << tret.getNode() << std::endl;
  Trace("tpp") << "TheoryPreprocessor::preprocess: return " << tret.getNode()
               << ", procLemmas=" << procLemmas
               << ", # lemmas = " << newLemmas.size() << std::endl;
  return tret;
}

TrustNode TheoryPreprocessor::preprocessLemma(
    TrustNode node, std::vector<SkolemLemma>& newLemmas)
{
  return preprocessLemmaInternal(node, newLemmas, true);
}

TrustNode TheoryPreprocessor::preprocessLemmaInternal(
    TrustNode node, std::vector<SkolemLemma>& newLemmas, bool procLemmas)
{
  // what was originally proven
  Node lemma = node.getProven();
  TrustNode tplemma = preprocessInternal(lemma, newLemmas, procLemmas);
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
    d_lp->addLazyStep(
        node.getProven(), node.getGenerator(), PfRule::THEORY_PREPROCESS_LEMMA);
    // only need to do anything if lemmap changed in a non-trivial way
    if (!CDProof::isSame(lemmap, lemma))
    {
      d_lp->addLazyStep(tplemma.getProven(),
                        tplemma.getGenerator(),
                        PfRule::THEORY_PREPROCESS,
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

RemoveTermFormulas& TheoryPreprocessor::getRemoveTermFormulas()
{
  return d_tfr;
}

TrustNode TheoryPreprocessor::theoryPreprocess(
    TNode assertion, std::vector<SkolemLemma>& newLemmas)
{
  std::unordered_set< std::pair<Node, uint32_t>, PairHashFunction<Node, uint32_t, std::hash<Node>> > wasPreprocessed;
  NodeManager* nm = NodeManager::currentNM();
  TCtxStack ctx(&d_rtfc);
  std::vector<bool> processedChildren;
  ctx.pushInitial(assertion);
  processedChildren.push_back(false);
  std::pair<Node, uint32_t> initial = ctx.getCurrent();
  std::pair<Node, uint32_t> curr;
  Node node;
  uint32_t nodeVal;
  TermFormulaCache::const_iterator itc;
  while (!ctx.empty())
  {
    curr = ctx.getCurrent();
    itc = d_tfCache.find(curr);
    node = curr.first;
    nodeVal = curr.second;
    Trace("rtf-debug") << "Visit " << node << ", " << nodeVal << std::endl;
    if (itc != d_tfCache.end())
    {
      Trace("rtf-debug") << "...already computed" << std::endl;
      ctx.pop();
      processedChildren.pop_back();
      if (wasPreprocessed.find(curr)!=wasPreprocessed.end())
      {
        // we preprocessed it to something else, carry that
        std::pair<Node, uint32_t> key(itc->second, nodeVal);
        itc = d_tfCache.find(key);
        Assert (itc!=d_tfCache.end());
        d_tfCache[curr] = itc->second;
        wasPreprocessed.erase(curr);
      }
      // already computed
      continue;
    }
    // if we have yet to process children
    if (!processedChildren.back())
    {
      size_t nchild = node.getNumChildren();
      if (nchild > 0)
      {
        if (node.isClosure())
        {
          // currently, we never do any term formula removal in quantifier bodies
        }
        else
        {
          Trace("rtf-debug") << "...recurse to children" << std::endl;
          // recurse if we have children
          processedChildren[processedChildren.size() - 1] = true;
          for (size_t i = 0; i < nchild; i++)
          {
            ctx.pushChild(node, nodeVal, i);
            processedChildren.push_back(false);
          }
          continue;
        }
      }
      else
      {
        Trace("rtf-debug") << "...base case" << std::endl;
        d_tfCache.insert(curr, node);
        ctx.pop();
        processedChildren.pop_back();
        continue;
      }
    }
    Trace("rtf-debug") << "...reconstruct" << std::endl;
    // otherwise, we are now finished processing children, pop the current node
    // and compute the result
    ctx.pop();
    processedChildren.pop_back();
    // if we have not already computed the result
    std::vector<Node> newChildren;
    bool childChanged = false;
    if (node.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      newChildren.push_back(node.getOperator());
    }
    // reconstruct from the children
    std::pair<Node, uint32_t> currChild;
    for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; i++)
    {
      // recompute the value of the child
      uint32_t val = d_rtfc.computeValue(node, nodeVal, i);
      currChild = std::pair<Node, uint32_t>(node[i], val);
      itc = d_tfCache.find(currChild);
      Assert(itc != d_tfCache.end());
      Node newChild = (*itc).second;
      Assert(!newChild.isNull());
      childChanged |= (newChild != node[i]);
      newChildren.push_back(newChild);
    }
    // If changes, we reconstruct the node
    Node ret = node;
    if (childChanged)
    {
      ret = nm->mkNode(node.getKind(), newChildren);
    }
    Node pret = preprocessWithProof(ret, newLemmas);
    if (pret!=ret)
    {
      // must restart
      ctx.push(node, nodeVal);
      processedChildren.push_back(true);
      ctx.push(pret, nodeVal);
      processedChildren.push_back(false);
      d_tfCache[curr] = pret;
      wasPreprocessed.insert(curr);
      continue;
    }
    // check if we should replace the current node
    TrustNode newLem;
    bool inQuant, inTerm;
    RtfTermContext::getFlags(nodeVal, inQuant, inTerm);
    Debug("ite") << "removeITEs(" << ret << ")"
                  << " " << inQuant << " " << inTerm << std::endl;
    Assert(!inQuant);
    TrustNode currTrn = d_tfr.runCurrent(ret, inTerm, newLem);
    // if we replaced by a skolem, we do not recurse
    if (!currTrn.isNull())
    {
      ret = currTrn.getNode();
      // if this is the first time we've seen this term, we have a new lemma
      // which we add to our vectors
      if (!newLem.isNull())
      {
        newLemmas.push_back(theory::SkolemLemma(newLem, ret));
      }
      Trace("rtf-debug") << "...replace by skolem" << std::endl;
    }
    // cache
    d_tfCache[curr] = ret;
    
  }
  itc = d_tfCache.find(initial);
  Assert(itc != d_tfCache.end());
  return TrustNode::mkTrustRewrite(assertion, (*itc).second, d_tpg.get());
}

// Recursively traverse a term and call the theory rewriter on its sub-terms
Node TheoryPreprocessor::ppTheoryRewrite(TNode term,
                                         std::vector<SkolemLemma>& lems)
{
  /*
  NodeMap::iterator find = d_ppCache.find(term);
  if (find != d_ppCache.end())
  {
    return (*find).second;
  }
  Node newTerm = term;
  if (term.getNumChildren() > 0)
  {
    // should be in rewritten form here
    Assert(term == Rewriter::rewrite(term));
    Trace("theory-pp") << "ppTheoryRewrite { " << term << endl;
    // do not rewrite inside quantifiers
    if (!term.isClosure())
    {
      NodeBuilder newNode(term.getKind());
      if (term.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        newNode << term.getOperator();
      }
      for (const Node& nt : term)
      {
        newNode << ppTheoryRewrite(nt, lems);
      }
      newTerm = Node(newNode);
      newTerm = rewriteWithProof(newTerm, d_tpg.get(), false);
    }
  }
  newTerm = preprocessWithProof(newTerm, lems);
  d_ppCache[term] = newTerm;
  Trace("theory-pp") << "ppTheoryRewrite returning " << newTerm << "}" << endl;
  return newTerm;
  */
  return term;
}

Node TheoryPreprocessor::rewriteWithProof(Node term,
                                          TConvProofGenerator* pg,
                                          bool isPre)
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
      pg->addRewriteStep(term, termr, PfRule::REWRITE, {}, {term}, isPre);
    }
  }
  return termr;
}

Node TheoryPreprocessor::preprocessWithProof(Node term,
                                             std::vector<SkolemLemma>& lems)
{
  // Important that it is in rewritten form, to ensure that the rewrite steps
  // recorded in d_tpg are functional. In other words, there should not
  // be steps from the same term to multiple rewritten forms, which would be
  // the case if we registered a preprocessing step for a non-rewritten term.
  Assert(term == Rewriter::rewrite(term));
  Trace("tpp-debug2") << "preprocessWithProof " << term
                      << ", #lems = " << lems.size() << std::endl;
  // We never call ppRewrite on equalities here, since equalities have a
  // special status. In particular, notice that theory preprocessing can be
  // called on all formulas asserted to theory engine, including those generated
  // as new literals appearing in lemmas. Calling ppRewrite on equalities is
  // incompatible with theory combination where a split on equality requested
  // by a theory could be preprocessed to something else, thus making theory
  // combination either non-terminating or result in solution soundness.
  // Notice that an alternative solution is to ensure that certain lemmas
  // (e.g. splits from theory combination) can never have theory preprocessing
  // applied to them. However, it is more uniform to say that theory
  // preprocessing is applied to all formulas. This makes it so that e.g.
  // theory solvers do not need to specify whether they want their lemmas to
  // be theory-preprocessed or not.
  if (term.getKind() == kind::EQUAL)
  {
    return term;
  }
  // call ppRewrite for the given theory
  TrustNode trn = d_engine.theoryOf(term)->ppRewrite(term, lems);
  Trace("tpp-debug2") << "preprocessWithProof returned " << trn
                      << ", #lems = " << lems.size() << std::endl;
  if (trn.isNull())
  {
    // no change, return
    return term;
  }
  Node termr = trn.getNode();
  Assert(term != termr);
  if (isProofEnabled())
  {
    registerTrustedRewrite(trn, d_tpg.get(), false);
  }
  // Rewrite again here, which notice is a *pre* rewrite.
  return rewriteWithProof(termr, d_tpg.get(), true);
}

bool TheoryPreprocessor::isProofEnabled() const { return d_tpg != nullptr; }

void TheoryPreprocessor::registerTrustedRewrite(TrustNode trn,
                                                TConvProofGenerator* pg,
                                                bool isPre)
{
  if (!isProofEnabled() || trn.isNull())
  {
    return;
  }
  Assert(trn.getKind() == TrustNodeKind::REWRITE);
  Node eq = trn.getProven();
  Node term = eq[0];
  Node termr = eq[1];
  if (trn.getGenerator() != nullptr)
  {
    Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (generator) "
                       << term << " -> " << termr << std::endl;
    trn.debugCheckClosed("tpp-debug",
                         "TheoryPreprocessor::preprocessWithProof");
    // always use term context hash 0 (default)
    pg->addRewriteStep(
        term, termr, trn.getGenerator(), isPre, PfRule::ASSUME, true);
  }
  else
  {
    Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (trusted) "
                       << term << " -> " << termr << std::endl;
    // small step trust
    pg->addRewriteStep(term,
                       termr,
                       PfRule::THEORY_PREPROCESS,
                       {},
                       {term.eqNode(termr)},
                       isPre);
  }
}

}  // namespace theory
}  // namespace cvc5
