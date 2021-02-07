/*********************                                                        */
/*! \file non_clausal_simp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Non-clausal simplification preprocessing pass.
 **
 ** Run the nonclausal solver and try to solve all assigned theory literals.
 **/

#include "preprocessing/passes/non_clausal_simp.h"

#include <vector>

#include "context/cdo.h"
#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

NonClausalSimp::Statistics::Statistics()
    : d_numConstantProps(
          "preprocessing::passes::NonClausalSimp::NumConstantProps", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numConstantProps);
}

NonClausalSimp::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numConstantProps);
}

/* -------------------------------------------------------------------------- */

NonClausalSimp::NonClausalSimp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "non-clausal-simp"),
      d_pnm(preprocContext->getProofNodeManager()),
      d_llpg(d_pnm ? new smt::PreprocessProofGenerator(
                         d_pnm,
                         preprocContext->getUserContext(),
                         "NonClausalSimp::llpg")
                   : nullptr),
      d_llra(d_pnm ? new LazyCDProof(d_pnm,
                                     nullptr,
                                     preprocContext->getUserContext(),
                                     "NonClausalSimp::llra")
                   : nullptr),
      d_tsubsList(preprocContext->getUserContext())
{
}

PreprocessingPassResult NonClausalSimp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(!options::unsatCores() || isProofEnabled())
      << "Unsat cores with non-clausal simp only supported with new proofs";

  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  theory::booleans::CircuitPropagator* propagator =
      d_preprocContext->getCircuitPropagator();

  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Trace("non-clausal-simplify") << "Assertion #" << i << " : "
                                  << (*assertionsToPreprocess)[i] << std::endl;
  }

  if (propagator->getNeedsFinish())
  {
    propagator->finish();
    propagator->setNeedsFinish(false);
  }
  propagator->initialize();

  // Assert all the assertions to the propagator
  Trace("non-clausal-simplify") << "asserting to propagator" << std::endl;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Assert(Rewriter::rewrite((*assertionsToPreprocess)[i])
           == (*assertionsToPreprocess)[i]);
    // Don't reprocess substitutions
    if (assertionsToPreprocess->isSubstsIndex(i))
    {
      continue;
    }
    Trace("non-clausal-simplify")
        << "asserting " << (*assertionsToPreprocess)[i] << std::endl;
    Debug("cores") << "propagator->assertTrue: " << (*assertionsToPreprocess)[i]
                   << std::endl;
    propagator->assertTrue((*assertionsToPreprocess)[i]);
  }

  Trace("non-clausal-simplify") << "propagating" << std::endl;
  TrustNode conf = propagator->propagate();
  if (!conf.isNull())
  {
    // If in conflict, just return false
    Trace("non-clausal-simplify")
        << "conflict in non-clausal propagation" << std::endl;
    assertionsToPreprocess->clear();
    assertionsToPreprocess->pushBackTrusted(conf);
    propagator->setNeedsFinish(true);
    return PreprocessingPassResult::CONFLICT;
  }

  Trace("non-clausal-simplify")
      << "Iterate through " << propagator->getLearnedLiterals().size()
      << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  context::Context* u = d_preprocContext->getUserContext();
  TrustSubstitutionMap& ttls = d_preprocContext->getTopLevelSubstitutions();
  CVC4_UNUSED SubstitutionMap& top_level_substs = ttls.get();
  // constant propagations
  std::shared_ptr<TrustSubstitutionMap> constantPropagations =
      std::make_shared<TrustSubstitutionMap>(
          u, d_pnm, "NonClausalSimp::cprop", PfRule::PREPROCESS_LEMMA);
  SubstitutionMap& cps = constantPropagations->get();
  // new substitutions
  std::shared_ptr<TrustSubstitutionMap> newSubstitutions =
      std::make_shared<TrustSubstitutionMap>(
          u, d_pnm, "NonClausalSimp::newSubs", PfRule::PREPROCESS_LEMMA);
  SubstitutionMap& nss = newSubstitutions->get();

  size_t j = 0;
  std::vector<TrustNode>& learned_literals = propagator->getLearnedLiterals();
  // if proofs are enabled, we will need to track the proofs of learned literals
  if (isProofEnabled())
  {
    d_tsubsList.push_back(constantPropagations);
    d_tsubsList.push_back(newSubstitutions);
    for (const TrustNode& tll : learned_literals)
    {
      d_llpg->notifyNewTrustedAssert(tll);
    }
  }
  for (size_t i = 0, size = learned_literals.size(); i < size; ++i)
  {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = learned_literals[i].getNode();
    Assert(Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Assert(top_level_substs.apply(learnedLiteral) == learnedLiteral);
    // process the learned literal with substitutions and const propagations
    learnedLiteral = processLearnedLit(
        learnedLiteral, newSubstitutions.get(), constantPropagations.get());
    Trace("non-clausal-simplify")
        << "Process learnedLiteral, after constProp : " << learnedLiteral
        << std::endl;
    // It might just simplify to a constant
    if (learnedLiteral.isConst())
    {
      if (learnedLiteral.getConst<bool>())
      {
        // If the learned literal simplifies to true, it's redundant
        continue;
      }
      else
      {
        // If the learned literal simplifies to false, we're in conflict
        Trace("non-clausal-simplify")
            << "conflict with " << learned_literals[i].getNode() << std::endl;
        assertionsToPreprocess->clear();
        Node n = NodeManager::currentNM()->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n, false, false, d_llpg.get());
        propagator->setNeedsFinish(true);
        return PreprocessingPassResult::CONFLICT;
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("non-clausal-simplify") << "solving " << learnedLiteral << std::endl;

    TrustNode tlearnedLiteral =
        TrustNode::mkTrustLemma(learnedLiteral, d_llpg.get());
    Theory::PPAssertStatus solveStatus =
        d_preprocContext->getTheoryEngine()->solve(tlearnedLiteral,
                                                   *newSubstitutions.get());

    switch (solveStatus)
    {
      case Theory::PP_ASSERT_STATUS_SOLVED:
      {
        // The literal should rewrite to true
        Trace("non-clausal-simplify")
            << "solved " << learnedLiteral << std::endl;
        Assert(Rewriter::rewrite(nss.apply(learnedLiteral)).isConst());
        // else fall through
        break;
      }
      case Theory::PP_ASSERT_STATUS_CONFLICT:
      {
        // If in conflict, we return false
        Trace("non-clausal-simplify")
            << "conflict while solving " << learnedLiteral << std::endl;
        assertionsToPreprocess->clear();
        Node n = NodeManager::currentNM()->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n);
        propagator->setNeedsFinish(true);
        return PreprocessingPassResult::CONFLICT;
      }
      default:
        if (learnedLiteral.getKind() == kind::EQUAL
            && (learnedLiteral[0].isConst() || learnedLiteral[1].isConst()))
        {
          // constant propagation
          TNode t;
          TNode c;
          if (learnedLiteral[0].isConst())
          {
            t = learnedLiteral[1];
            c = learnedLiteral[0];
          }
          else
          {
            t = learnedLiteral[0];
            c = learnedLiteral[1];
          }
          Assert(!t.isConst());
          Assert(cps.apply(t) == t);
          Assert(top_level_substs.apply(t) == t);
          Assert(nss.apply(t) == t);
          // also add to learned literal
          ProofGenerator* cpg = constantPropagations->addSubstitutionSolved(
              t, c, tlearnedLiteral);
          // We need to justify (= t c) as a literal, since it is reasserted
          // to the assertion pipeline below. We do this with the proof
          // generator returned by the above call.
          if (isProofEnabled())
          {
            d_llpg->notifyNewAssert(t.eqNode(c), cpg);
          }
        }
        else
        {
          // Keep the literal
          learned_literals[j++] = learned_literals[i];
        }
        break;
    }
  }

#ifdef CVC4_ASSERTIONS
  // NOTE: When debugging this code, consider moving this check inside of the
  // loop over propagator->getLearnedLiterals(). This check has been moved
  // outside because it is costly for certain inputs (see bug 508).
  //
  // Check data structure invariants:
  // 1. for each lhs of top_level_substs, does not appear anywhere in rhs of
  // top_level_substs or anywhere in constantPropagations
  // 2. each lhs of constantPropagations rewrites to itself
  // 3. if l -> r is a constant propagation and l is a subterm of l' with l' ->
  // r' another constant propagation, then l'[l/r] -> r' should be a
  //    constant propagation too
  // 4. each lhs of constantPropagations is different from each rhs
  for (SubstitutionMap::iterator pos = nss.begin(); pos != nss.end(); ++pos)
  {
    Assert((*pos).first.isVar());
    Assert(top_level_substs.apply((*pos).first) == (*pos).first);
    Assert(top_level_substs.apply((*pos).second) == (*pos).second);
    Node app = nss.apply((*pos).second);
    Assert(nss.apply(app) == app);
  }
  for (SubstitutionMap::iterator pos = cps.begin(); pos != cps.end(); ++pos)
  {
    Assert((*pos).second.isConst());
    Assert(Rewriter::rewrite((*pos).first) == (*pos).first);
    Assert(cps.apply((*pos).second) == (*pos).second);
  }
#endif /* CVC4_ASSERTIONS */

  // Resize the learnt
  Trace("non-clausal-simplify")
      << "Resize non-clausal learned literals to " << j << std::endl;
  learned_literals.resize(j);

  unordered_set<TNode, TNodeHashFunction> s;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node assertion = (*assertionsToPreprocess)[i];
    TrustNode assertionNew = newSubstitutions->apply(assertion);
    Trace("non-clausal-simplify") << "assertion = " << assertion << std::endl;
    if (!assertionNew.isNull())
    {
      Trace("non-clausal-simplify")
          << "assertionNew = " << assertionNew.getNode() << std::endl;
      assertionsToPreprocess->replaceTrusted(i, assertionNew);
      assertion = assertionNew.getNode();
      Assert(Rewriter::rewrite(assertion) == assertion);
    }
    for (;;)
    {
      assertionNew = constantPropagations->apply(assertion);
      if (assertionNew.isNull())
      {
        break;
      }
      Assert(assertionNew.getNode() != assertion);
      assertionsToPreprocess->replaceTrusted(i, assertionNew);
      assertion = assertionNew.getNode();
      d_statistics.d_numConstantProps += 1;
      Trace("non-clausal-simplify")
          << "assertionNew = " << assertion << std::endl;
    }
    s.insert(assertion);
    Trace("non-clausal-simplify")
        << "non-clausal preprocessed: " << assertion << std::endl;
  }

  // add substitutions to model, or as assertions if needed (when incremental)
  TheoryModel* m = d_preprocContext->getTheoryEngine()->getModel();
  Assert(m != nullptr);
  NodeManager* nm = NodeManager::currentNM();
  for (SubstitutionMap::iterator pos = nss.begin(); pos != nss.end(); ++pos)
  {
    Node lhs = (*pos).first;
    TrustNode trhs = newSubstitutions->apply((*pos).second);
    Node rhs = trhs.isNull() ? (*pos).second : trhs.getNode();
    // If using incremental, we must check whether this variable has occurred
    // before now. If it hasn't we can add this as a substitution.
    if (!assertionsToPreprocess->storeSubstsInAsserts()
        || d_preprocContext->getSymsInAssertions().find(lhs)
               == d_preprocContext->getSymsInAssertions().end())
    {
      Trace("non-clausal-simplify")
          << "substitute: " << lhs << " " << rhs << std::endl;
      m->addSubstitution(lhs, rhs);
    }
    else
    {
      // if it has, the substitution becomes an assertion
      Node eq = nm->mkNode(kind::EQUAL, lhs, rhs);
      Trace("non-clausal-simplify")
          << "substitute: will notify SAT layer of substitution: " << eq
          << std::endl;
       trhs = newSubstitutions->apply((*pos).first);
       Assert(!trhs.isNull());
       assertionsToPreprocess->addSubstitutionNode(trhs.getProven(),
       trhs.getGenerator());
    }
  }

  Assert(assertionsToPreprocess->getRealAssertionsEnd()
         <= assertionsToPreprocess->size());
  // Learned literals to conjoin. If proofs are enabled, all these are
  // justified by d_llpg.
  std::vector<Node> learnedLitsToConjoin;

  for (size_t i = 0; i < learned_literals.size(); ++i)
  {
    Node learned = learned_literals[i].getNode();
    Assert(top_level_substs.apply(learned) == learned);
    // process learned literal
    learned = processLearnedLit(
        learned, newSubstitutions.get(), constantPropagations.get());
    if (s.find(learned) != s.end())
    {
      continue;
    }
    s.insert(learned);
    learnedLitsToConjoin.push_back(learned);
    Trace("non-clausal-simplify")
        << "non-clausal learned : " << learned << std::endl;
  }
  learned_literals.clear();

  for (SubstitutionMap::iterator pos = cps.begin(); pos != cps.end(); ++pos)
  {
    Node cProp = (*pos).first.eqNode((*pos).second);
    Assert(top_level_substs.apply(cProp) == cProp);
    // process learned literal (substitutions only)
    cProp = processLearnedLit(cProp, newSubstitutions.get(), nullptr);
    if (s.find(cProp) != s.end())
    {
      continue;
    }
    s.insert(cProp);
    learnedLitsToConjoin.push_back(cProp);
    Trace("non-clausal-simplify")
        << "non-clausal constant propagation : " << cProp << std::endl;
  }

  // Add new substitutions to topLevelSubstitutions
  // Note that we don't have to keep rhs's in full solved form
  // because SubstitutionMap::apply does a fixed-point iteration when
  // substituting
  ttls.addSubstitutions(*newSubstitutions.get());

  if (!learnedLitsToConjoin.empty())
  {
    size_t replIndex = assertionsToPreprocess->getRealAssertionsEnd() - 1;
    Node newConj = NodeManager::currentNM()->mkAnd(learnedLitsToConjoin);
    Trace("non-clausal-simplify")
        << "non-clausal simplification, reassert: " << newConj << std::endl;
    ProofGenerator* pg = nullptr;
    if (isProofEnabled())
    {
      // justify in d_llra
      for (const Node& lit : learnedLitsToConjoin)
      {
        d_llra->addLazyStep(lit, d_llpg.get());
      }
      if (learnedLitsToConjoin.size() > 1)
      {
        d_llra->addStep(newConj, PfRule::AND_INTRO, learnedLitsToConjoin, {});
        pg = d_llra.get();
      }
      else
      {
        // otherwise we ask the learned literal proof generator directly
        pg = d_llpg.get();
      }
    }
    // ------- from d_llpg    --------- from d_llpg
    //  conj[0]       ....    d_conj[n]
    // -------------------------------- AND_INTRO
    //  newConj
    // where newConj is conjoined at the given index
    assertionsToPreprocess->conjoin(replIndex, newConj, pg);
  }

  propagator->setNeedsFinish(true);
  return PreprocessingPassResult::NO_CONFLICT;
}

bool NonClausalSimp::isProofEnabled() const { return d_pnm != nullptr; }

Node NonClausalSimp::processLearnedLit(Node lit,
                                       theory::TrustSubstitutionMap* subs,
                                       theory::TrustSubstitutionMap* cp)
{
  TrustNode tlit;
  if (subs != nullptr)
  {
    tlit = subs->apply(lit);
    if (!tlit.isNull())
    {
      lit = processRewrittenLearnedLit(tlit);
    }
    Trace("non-clausal-simplify")
        << "Process learnedLiteral, after newSubs : " << lit << std::endl;
  }
  // apply to fixed point
  if (cp != nullptr)
  {
    for (;;)
    {
      tlit = cp->apply(lit);
      if (tlit.isNull())
      {
        break;
      }
      Assert(lit != tlit.getNode());
      lit = processRewrittenLearnedLit(tlit);
      d_statistics.d_numConstantProps += 1;
    }
  }
  return lit;
}

Node NonClausalSimp::processRewrittenLearnedLit(theory::TrustNode trn)
{
  if (isProofEnabled())
  {
    d_llpg->notifyTrustedPreprocessed(trn);
  }
  // return the node
  return trn.getNode();
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
