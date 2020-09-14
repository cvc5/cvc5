/*********************                                                        */
/*! \file ite_simp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ITE simplification preprocessing pass.
 **/

#include "preprocessing/passes/ite_simp.h"

#include <vector>

#include "smt/smt_statistics_registry.h"
#include "smt_util/nary_builder.h"
#include "theory/arith/arith_ite_utils.h"

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace {

Node simpITE(util::ITEUtilities* ite_utils, TNode assertion)
{
  if (!ite_utils->containsTermITE(assertion))
  {
    return assertion;
  }
  else
  {
    Node result = ite_utils->simpITE(assertion);
    Node res_rewritten = Rewriter::rewrite(result);

    if (options::simplifyWithCareEnabled())
    {
      Chat() << "starting simplifyWithCare()" << endl;
      Node postSimpWithCare = ite_utils->simplifyWithCare(res_rewritten);
      Chat() << "ending simplifyWithCare()"
             << " post simplifyWithCare()" << postSimpWithCare.getId() << endl;
      result = Rewriter::rewrite(postSimpWithCare);
    }
    else
    {
      result = res_rewritten;
    }
    return result;
  }
}

/**
 * Ensures the assertions asserted after index 'before' now effectively come
 * before 'real_assertions_end'.
 */
void compressBeforeRealAssertions(AssertionPipeline* assertionsToPreprocess,
                                  size_t before)
{
  size_t cur_size = assertionsToPreprocess->size();
  if (before >= cur_size || assertionsToPreprocess->getRealAssertionsEnd() <= 0
      || assertionsToPreprocess->getRealAssertionsEnd() >= cur_size)
  {
    return;
  }

  // assertions
  // original: [0 ... assertionsToPreprocess.getRealAssertionsEnd())
  //  can be modified
  // ites skolems [assertionsToPreprocess.getRealAssertionsEnd(), before)
  //  cannot be moved
  // added [before, cur_size)
  //  can be modified
  Assert(0 < assertionsToPreprocess->getRealAssertionsEnd());
  Assert(assertionsToPreprocess->getRealAssertionsEnd() <= before);
  Assert(before < cur_size);

  std::vector<Node> intoConjunction;
  for (size_t i = before; i < cur_size; ++i)
  {
    intoConjunction.push_back((*assertionsToPreprocess)[i]);
  }
  assertionsToPreprocess->resize(before);
  size_t lastBeforeItes = assertionsToPreprocess->getRealAssertionsEnd() - 1;
  intoConjunction.push_back((*assertionsToPreprocess)[lastBeforeItes]);
  Node newLast = CVC4::util::NaryBuilder::mkAssoc(kind::AND, intoConjunction);
  assertionsToPreprocess->replace(lastBeforeItes, newLast);
  Assert(assertionsToPreprocess->size() == before);
}

}  // namespace

/* -------------------------------------------------------------------------- */

ITESimp::Statistics::Statistics()
    : d_arithSubstitutionsAdded(
          "preprocessing::passes::ITESimp::ArithSubstitutionsAdded", 0)
{
  smtStatisticsRegistry()->registerStat(&d_arithSubstitutionsAdded);
}

ITESimp::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_arithSubstitutionsAdded);
}

bool ITESimp::doneSimpITE(AssertionPipeline* assertionsToPreprocess)
{
  // This pass does not support dependency tracking yet
  // (learns substitutions from all assertions so just
  // adding addDependence is not enough)
  if (options::unsatCores())
  {
    return true;
  }
  bool result = true;
  bool simpDidALotOfWork = d_iteUtilities.simpIteDidALotOfWorkHeuristic();
  if (simpDidALotOfWork)
  {
    if (options::compressItes())
    {
      result = d_iteUtilities.compress(assertionsToPreprocess->ref());
    }

    if (result)
    {
      // if false, don't bother to reclaim memory here.
      NodeManager* nm = NodeManager::currentNM();
      if (nm->poolSize() >= options::zombieHuntThreshold())
      {
        Chat() << "..ite simplifier did quite a bit of work.. "
               << nm->poolSize() << endl;
        Chat() << "....node manager contains " << nm->poolSize()
               << " nodes before cleanup" << endl;
        d_iteUtilities.clear();
        Rewriter::clearCaches();
        nm->reclaimZombiesUntil(options::zombieHuntThreshold());
        Chat() << "....node manager contains " << nm->poolSize()
               << " nodes after cleanup" << endl;
      }
    }
  }

  // Do theory specific preprocessing passes
  TheoryEngine* theory_engine = d_preprocContext->getTheoryEngine();
  if (theory_engine->getLogicInfo().isTheoryEnabled(theory::THEORY_ARITH)
      && !options::incrementalSolving())
  {
    if (!simpDidALotOfWork)
    {
      util::ContainsTermITEVisitor& contains =
          *(d_iteUtilities.getContainsVisitor());
      arith::ArithIteUtils aiteu(contains,
                                 d_preprocContext->getUserContext(),
                                 theory_engine->getModel());
      bool anyItes = false;
      for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
      {
        Node curr = (*assertionsToPreprocess)[i];
        if (contains.containsTermITE(curr))
        {
          anyItes = true;
          Node res = aiteu.reduceVariablesInItes(curr);
          Debug("arith::ite::red") << "@ " << i << " ... " << curr << endl
                                   << "   ->" << res << endl;
          if (curr != res)
          {
            Node more = aiteu.reduceConstantIteByGCD(res);
            Debug("arith::ite::red") << "  gcd->" << more << endl;
            (*assertionsToPreprocess)[i] = Rewriter::rewrite(more);
          }
        }
      }
      if (!anyItes)
      {
        unsigned prevSubCount = aiteu.getSubCount();
        aiteu.learnSubstitutions(assertionsToPreprocess->ref());
        if (prevSubCount < aiteu.getSubCount())
        {
          d_statistics.d_arithSubstitutionsAdded +=
              aiteu.getSubCount() - prevSubCount;
          bool anySuccess = false;
          for (size_t i = 0, N = assertionsToPreprocess->size(); i < N; ++i)
          {
            Node curr = (*assertionsToPreprocess)[i];
            Node next = Rewriter::rewrite(aiteu.applySubstitutions(curr));
            Node res = aiteu.reduceVariablesInItes(next);
            Debug("arith::ite::red") << "@ " << i << " ... " << next << endl
                                     << "   ->" << res << endl;
            Node more = aiteu.reduceConstantIteByGCD(res);
            Debug("arith::ite::red") << "  gcd->" << more << endl;
            if (more != next)
            {
              anySuccess = true;
              break;
            }
          }
          for (size_t i = 0, N = assertionsToPreprocess->size();
               anySuccess && i < N;
               ++i)
          {
            Node curr = (*assertionsToPreprocess)[i];
            Node next = Rewriter::rewrite(aiteu.applySubstitutions(curr));
            Node res = aiteu.reduceVariablesInItes(next);
            Debug("arith::ite::red") << "@ " << i << " ... " << next << endl
                                     << "   ->" << res << endl;
            Node more = aiteu.reduceConstantIteByGCD(res);
            Debug("arith::ite::red") << "  gcd->" << more << endl;
            (*assertionsToPreprocess)[i] = Rewriter::rewrite(more);
          }
        }
      }
    }
  }
  return result;
}

/* -------------------------------------------------------------------------- */

ITESimp::ITESimp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-simp")
{
}

PreprocessingPassResult ITESimp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  size_t nasserts = assertionsToPreprocess->size();
  for (size_t i = 0; i < nasserts; ++i)
  {
    d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);
    Node simp = simpITE(&d_iteUtilities, (*assertionsToPreprocess)[i]);
    assertionsToPreprocess->replace(i, simp);
    if (simp.isConst() && !simp.getConst<bool>())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  bool done = doneSimpITE(assertionsToPreprocess);
  if (nasserts < assertionsToPreprocess->size())
  {
    compressBeforeRealAssertions(assertionsToPreprocess, nasserts);
  }
  return done ? PreprocessingPassResult::NO_CONFLICT
              : PreprocessingPassResult::CONFLICT;
}


/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
