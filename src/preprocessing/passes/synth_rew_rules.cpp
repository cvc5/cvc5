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

  // compute the variables we will be sampling
  std::vector<Node> vars;
  unsigned nsamples = options::sygusSamples();

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();

  // attribute to mark processed terms
  SynthRrComputedAttribute srrca;

  // initialize the candidate rewrite
  std::unique_ptr<theory::quantifiers::CandidateRewriteDatabaseGen> crdg;
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  // two passes: the first collects the variables, the second registers the
  // terms
  for (unsigned r = 0; r < 2; r++)
  {
    visited.clear();
    visit.clear();
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
            Trace("synth-rr-pass-debug")
                << "...children are valid, check rewrites..." << std::endl;
            if (r == 0)
            {
              if (cur.isVar())
              {
                vars.push_back(cur);
              }
            }
            else
            {
              Trace("synth-rr-pass-debug") << "Add term " << cur << std::endl;
              // mark as processed
              cur.setAttribute(srrca, true);
              bool ret = crdg->addTerm(cur, *nodeManagerOptions.getOut());
              Trace("synth-rr-pass-debug") << "...return " << ret << std::endl;
              // if we want only rewrites of minimal size terms, we would set
              // childrenValid to false if ret is false here.
            }
          }
          visited[cur] = childrenValid;
        }
      } while (!visit.empty());
    }
    if (r == 0)
    {
      Trace("synth-rr-pass-debug")
          << "Initialize with " << nsamples
          << " samples and variables : " << vars << std::endl;
      crdg = std::unique_ptr<theory::quantifiers::CandidateRewriteDatabaseGen>(
          new theory::quantifiers::CandidateRewriteDatabaseGen(vars, nsamples));
    }
  }

  Trace("synth-rr-pass") << "...finished " << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
