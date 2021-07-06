/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriting based on learned literals
 */

#include "preprocessing/passes/learned_rewrite.h"

#include "expr/skolem_manager.h"
#include "expr/term_context_stack.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

const char* toString(LearnedRewriteId i)
{
  switch (i)
  {
    case LearnedRewriteId::NON_ZERO_DEN: return "NON_ZERO_DEN";
    case LearnedRewriteId::INT_MOD_RANGE: return "INT_MOD_RANGE";
    case LearnedRewriteId::PRED_POS_LB: return "PRED_POS_LB";
    case LearnedRewriteId::PRED_ZERO_LB: return "PRED_ZERO_LB";
    case LearnedRewriteId::PRED_NEG_UB: return "PRED_NEG_UB";
    case LearnedRewriteId::NONE: return "NONE";
    default: return "?LearnedRewriteId?";
  }
}

std::ostream& operator<<(std::ostream& out, LearnedRewriteId i)
{
  out << toString(i);
  return out;
}

LearnedRewrite::LearnedRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "learned-rewrite"),
      d_lrewCount(smtStatisticsRegistry().registerHistogram<LearnedRewriteId>(
          "LearnedRewrite::lrewCount"))
{
}

PreprocessingPassResult LearnedRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  arith::BoundInference binfer;
  std::vector<Node> learnedLits = d_preprocContext->getLearnedLiterals();
  std::unordered_set<Node> llrw;
  std::unordered_map<TNode, Node> visited;
  if (learnedLits.empty())
  {
    Trace("learned-rewrite-ll") << "No learned literals" << std::endl;
    return PreprocessingPassResult::NO_CONFLICT;
  }
  else
  {
    Trace("learned-rewrite-ll") << "Learned literals:" << std::endl;
    for (const Node& l : learnedLits)
    {
      // maybe use the literal for bound inference?
      Kind k = l.getKind();
      Assert (k != LT && k != GT && k != LEQ);
      if (k == EQUAL || k == GEQ)
      {
        binfer.add(l);
      }
      Trace("learned-rewrite-ll") << "- " << l << std::endl;
    }
    const std::map<Node, arith::Bounds>& bs = binfer.get();
    // get the literals that were critical, i.e. used in the derivation of a
    // bound
    for (const std::pair<const Node, arith::Bounds>& b : bs)
    {
      for (size_t i = 0; i < 2; i++)
      {
        Node origin = i == 0 ? b.second.lower_origin : b.second.upper_origin;
        if (!origin.isNull())
        {
          llrw.insert(origin);
        }
      }
    }
    // rewrite the non-critical learned literals, some may be redundant
    for (const Node& l : learnedLits)
    {
      if (llrw.find(l) != llrw.end())
      {
        continue;
      }
      Node e = rewriteLearnedRec(l, binfer, llrw, visited);
      if (e.isConst())
      {
        // ignore true
        if (e.getConst<bool>())
        {
          continue;
        }
        // conflict, we are done
        assertionsToPreprocess->push_back(e);
        return PreprocessingPassResult::CONFLICT;
      }
      llrw.insert(e);
    }
    Trace("learned-rewrite-ll") << "end" << std::endl;
  }
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Trace("learned-rewrite-assert")
        << "LearnedRewrite: assert: " << prev << std::endl;
    Node e = rewriteLearnedRec(prev, binfer, llrw, visited);
    if (e != prev)
    {
      Trace("learned-rewrite-assert")
          << ".......................: " << e << std::endl;
      assertionsToPreprocess->replace(i, e);
    }
  }
  // Add the conjunction of learned literals back to assertions. Notice that
  // in some cases we may add top-level assertions back to the assertion list
  // unchanged.
  if (!llrw.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> llrvec(llrw.begin(), llrw.end());
    Node llc = nm->mkAnd(llrvec);
    Trace("learned-rewrite-assert")
        << "Re-add rewritten learned conjunction: " << llc << std::endl;
    assertionsToPreprocess->push_back(llc);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node LearnedRewrite::rewriteLearnedRec(Node n,
                                       arith::BoundInference& binfer,
                                       std::unordered_set<Node>& lems,
                                       std::unordered_map<TNode, Node>& visited)
{
  return n;
}

Node LearnedRewrite::rewriteLearned(Node n,
                                    arith::BoundInference& binfer,
                                    std::unordered_set<Node>& lems)
{
  return n;
}

Node LearnedRewrite::returnRewriteLearned(Node n, Node nr, LearnedRewriteId id)
{
  if (Trace.isOn("learned-rewrite"))
  {
    Trace("learned-rewrite") << "LearnedRewrite::Rewrite: (" << id << ") " << n
                             << " == " << nr << std::endl;
  }
  d_lrewCount << id;
  return nr;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
