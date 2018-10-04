/*********************                                                        */
/*! \file synth_rew_rules.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A technique for synthesizing candidate rewrites of the form t1 = t2,
 ** where t1 and t2 are subterms of the input.
 **/

#include "preprocessing/passes/synth_rew_rules.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/candidate_rewrite_database.h"

using namespace std;

namespace CVC4 {
namespace preprocessing {
namespace passes {

// Attribute for whether we have computed rewrite rules for a given term.
// Notice that this currently must be a global attribute, since if
// we've computed rewrites for a term, we should not compute rewrites for the
// same term in a subcall to another SmtEngine (for instance, when using
// "exact" equivalence checking).
struct SynthRrComputedAttributeId
{
};
typedef expr::Attribute<SynthRrComputedAttributeId, bool>
    SynthRrComputedAttribute;

SynthRewRulesPass::SynthRewRulesPass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "synth-rr"){};

PreprocessingPassResult SynthRewRulesPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Trace("synth-rr-pass") << "Synthesize rewrite rules from assertions..."
                         << std::endl;
  std::vector<Node>& assertions = assertionsToPreprocess->ref();

  NodeManager* nm = NodeManager::currentNM();

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();

  // attribute to mark processed terms
  SynthRrComputedAttribute srrca;

  // initialize the candidate rewrite
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  // Get all usable terms from the input. A term is usable if it does not
  // contain a quantified subterm
  std::vector<Node> terms;
  TNode cur;
  for (const Node& a : assertions)
  {
    visit.push_back(a);
    do
    {
      cur = visit.back();
      visit.pop_back();
      it = visited.find(cur);
      // if already processed, ignore
      if (cur.getAttribute(SynthRrComputedAttribute()))
      {
        Trace("synth-rr-pass-debug")
            << "...already processed " << cur << std::endl;
      }
      else if (it == visited.end())
      {
        Trace("synth-rr-pass-debug") << "...preprocess " << cur << std::endl;
        visited[cur] = false;
        Kind k = cur.getKind();
        bool isQuant = k == kind::FORALL || k == kind::EXISTS
                       || k == kind::LAMBDA || k == kind::CHOICE;
        // we recurse on this node if it is not a quantified formula
        if (!isQuant)
        {
          visit.push_back(cur);
          for (const Node& cc : cur)
          {
            visit.push_back(cc);
          }
        }
      }
      else if (!it->second)
      {
        Trace("synth-rr-pass-debug") << "...postprocess " << cur << std::endl;
        // check if all of the children are valid
        // this ensures we do not register terms that have e.g. quantified
        // formulas as subterms
        bool childrenValid = true;
        for (const Node& cc : cur)
        {
          Assert(visited.find(cc) != visited.end());
          if (!visited[cc])
          {
            childrenValid = false;
          }
        }
        if (childrenValid)
        {
          Trace("synth-rr-pass-debug") << "...children are valid" << std::endl;
          Trace("synth-rr-pass-debug") << "Add term " << cur << std::endl;
          terms.push_back(cur);
          // mark as processed
          cur.setAttribute(srrca, true);
        }
        visited[cur] = childrenValid;
      }
    } while (!visit.empty());
  }
  // We've collected all terms in the input. We will produce skeletons from
  // these terms. We start by constructing a fixed number of variables per
  // type.
  unsigned nvars = 3;
  std::map<TypeNode, std::vector<Node> > tvars;
  std::vector<Node> allVars;
  for (const Node& n : terms)
  {
    TypeNode tn = n.getType();
    if (tvars.find(tn) == tvars.end())
    {
      for (unsigned i = 0; i < nvars; i++)
      {
        Node v = nm->mkBoundVar(tn);
        tvars[tn].push_back(v);
        allVars.push_back(v);
      }
    }
  }
  Trace("synth-rr-pass")
      << "Initialize the candidate rewrite database generator..." << std::endl;
  unsigned nsamples = options::sygusSamples();
  std::unique_ptr<theory::quantifiers::CandidateRewriteDatabaseGen> crdg;
  crdg.reset(
      new theory::quantifiers::CandidateRewriteDatabaseGen(allVars, nsamples));

  // now, we increment skeleton sizes until a fixed point is reached
  bool success = false;
  unsigned skSize = 0;
  std::vector<Node> termsNext;
  do
  {
    success = false;
    std::unordered_set<Node, NodeHashFunction> cacheGenTerms;
    if (skSize == 0)
    {
      // optimization: just take the variables directly
      for (const Node& v : allVars)
      {
        if (crdg->addTerm(v, *nodeManagerOptions.getOut()))
        {
          success = true;
        }
      }
    }
    else
    {
      for (const Node& t : terms)
      {
        std::unordered_set<Node, NodeHashFunction> genTerms;
        if (getTermSkeletons(t, skSize, tvars, cacheGenTerms, genTerms))
        {
          // Only if term skeletons were possible to generate do we keep t
          // for the next round. This ensures we do not keep retrying to
          // generate skeletons from terms whose size is less than skSize.
          termsNext.push_back(t);
        }
        for (const Node& cgt : genTerms)
        {
          if (crdg->addTerm(cgt, *nodeManagerOptions.getOut()))
          {
            success = true;
          }
          cacheGenTerms.insert(cgt);
        }
      }
    }
    if (success)
    {
      skSize++;
      terms.clear();
      terms.insert(terms.end(), termsNext.begin(), termsNext.end());
      termsNext.clear();
    }
  } while (success);

  /*
  bool ret = crdg->addTerm(cur, *nodeManagerOptions.getOut());
  Trace("synth-rr-pass-debug") << "...return " << ret << std::endl;
  // if we want only rewrites of minimal size terms, we would set
  // childrenValid to false if ret is false here.
  */

  Trace("synth-rr-pass") << "...finished " << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

bool SynthRewRulesPass::getTermSkeletons(
    Node t,
    unsigned tsize,
    const std::map<TypeNode, std::vector<Node> >& tvars,
    const std::unordered_set<Node, NodeHashFunction>& cacheGenTerms,
    std::unordered_set<Node, NodeHashFunction>& genTerms)
{
  return false;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
