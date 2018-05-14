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
 ** \brief synth_rew_rules pass
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

  // initialize the candidate rewrite
  std::unique_ptr<theory::quantifiers::CandidateRewriteDatabaseGen> crdg;
  // two passes: the first collects the variables, the second registers the
  // terms
  for (unsigned r = 0; r < 2; r++)
  {
    std::unordered_set<TNode, TNodeHashFunction> visited;
    TNode cur;
    for (const Node& a : assertions)
    {
      std::vector<TNode> visit;
      visit.push_back(a);
      do
      {
        cur = visit.back();
        visit.pop_back();
        if (visited.find(cur) == visited.end())
        {
          visited.insert(cur);
          Kind k = cur.getKind();
          bool isQuant = k == kind::FORALL || k == kind::EXISTS
                         || k == kind::LAMBDA || k == kind::CHOICE;
          if (!isQuant)
          {
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
              bool ret = crdg->addTerm(cur, *nodeManagerOptions.getOut());
              Trace("synth-rr-pass-debug") << "...return " << ret << std::endl;
            }
            for (const Node& cn : cur)
            {
              visit.push_back(cn);
            }
          }
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
