/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Non-clausal simplification preprocessing pass.
 *
 * Run the nonclausal solver and try to solve all assigned theory literals.
 */

#include "preprocessing/passes/non_clausal_simp.h"

#include <vector>

#include "context/cdo.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/preprocess_proof_generator.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

NonClausalSimp::Statistics::Statistics(StatisticsRegistry& reg)
    : d_numConstantProps(reg.registerInt(
        "preprocessing::passes::NonClausalSimp::NumConstantProps"))
{
}


/* -------------------------------------------------------------------------- */

NonClausalSimp::NonClausalSimp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "non-clausal-simp"),
      d_statistics(statisticsRegistry()),
      d_llpg(options().smt.produceProofs ? new smt::PreprocessProofGenerator(
                 d_env, userContext(), "NonClausalSimp::llpg")
                                         : nullptr),
      d_llra(options().smt.produceProofs ? new LazyCDProof(
                 d_env, nullptr, userContext(), "NonClausalSimp::llra")
                                         : nullptr),
      d_tsubsList(userContext())
{
}

PreprocessingPassResult NonClausalSimp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  if (TraceIsOn("non-clausal-simplify"))
  {
    for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
    {
      Trace("non-clausal-simplify")
          << "Assertion #" << i << " : " << (*assertionsToPreprocess)[i]
          << std::endl;
    }
  }

  theory::booleans::CircuitPropagator* propagator =
      d_preprocContext->getCircuitPropagator();
  propagator->initialize();

  // Assert all the assertions to the propagator
  Trace("non-clausal-simplify") << "asserting to propagator" << std::endl;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Assert(rewrite((*assertionsToPreprocess)[i])
           == (*assertionsToPreprocess)[i]) << (*assertionsToPreprocess)[i];
    // Don't reprocess substitutions
    if (assertionsToPreprocess->isSubstsIndex(i))
    {
      continue;
    }
    Trace("non-clausal-simplify")
        << "asserting " << (*assertionsToPreprocess)[i] << std::endl;
    Trace("cores") << "propagator->assertTrue: " << (*assertionsToPreprocess)[i]
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
    return PreprocessingPassResult::CONFLICT;
  }

  Trace("non-clausal-simplify")
      << "Iterate through " << propagator->getLearnedLiterals().size()
      << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  NodeManager* nm = NodeManager::currentNM();
  context::Context* u = userContext();
  Rewriter* rw = d_env.getRewriter();
  TrustSubstitutionMap& ttls = d_preprocContext->getTopLevelSubstitutions();
  CVC5_UNUSED SubstitutionMap& top_level_substs = ttls.get();
  // constant propagations
  std::shared_ptr<TrustSubstitutionMap> constantPropagations =
      std::make_shared<TrustSubstitutionMap>(
          d_env, u, "NonClausalSimp::cprop", PfRule::PREPROCESS_LEMMA);
  SubstitutionMap& cps = constantPropagations->get();
  // new substitutions
  std::shared_ptr<TrustSubstitutionMap> newSubstitutions =
      std::make_shared<TrustSubstitutionMap>(
          d_env, u, "NonClausalSimp::newSubs", PfRule::PREPROCESS_LEMMA);
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
    Trace("non-clausal-simplify")
        << "Process learnedLiteral : " << learnedLiteral;
    Assert(rewrite(learnedLiteral) == learnedLiteral);
    Assert(top_level_substs.apply(learnedLiteral) == learnedLiteral)
        << learnedLiteral << " after subs is "
        << top_level_substs.apply(learnedLiteral);
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
        Node n = nm->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n, false, d_llpg.get());
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
        Assert(rewrite(nss.apply(learnedLiteral)).isConst());
        // else fall through
        break;
      }
      case Theory::PP_ASSERT_STATUS_CONFLICT:
      {
        // If in conflict, we return false
        Trace("non-clausal-simplify")
            << "conflict while solving " << learnedLiteral << std::endl;
        assertionsToPreprocess->clear();
        Node n = nm->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n);
        return PreprocessingPassResult::CONFLICT;
      }
      default:
        TNode t;
        TNode c;
        if (learnedLiteral.getKind() == kind::EQUAL
            && (learnedLiteral[0].isConst() || learnedLiteral[1].isConst()))
        {
          // constant propagation
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
        }
        else if (options().smt.simplificationBoolConstProp)
        {
          // From non-equalities, learn the Boolean equality. Notice that
          // the equality case above is strictly more powerful that this, since
          // e.g. (= t c) * { t -> c } also simplifies to true.
          bool pol = learnedLiteral.getKind() != kind::NOT;
          c = nm->mkConst(pol);
          t = pol ? learnedLiteral : learnedLiteral[0];
        }
        if (!t.isNull())
        {
          Assert(!t.isConst());
          Assert(rewrite(cps.apply(t)) == t);
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
          // Keep the learned literal
          learned_literals[j++] = learned_literals[i];
        }
        // Its a literal that could not be processed as a substitution or
        // conflict. In this case, we notify the context of the learned
        // literal, which will process it with the learned literal manager.
        d_preprocContext->notifyLearnedLiteral(learnedLiteral);
        break;
    }
  }

#ifdef CVC5_ASSERTIONS
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
    Assert(rewrite((*pos).first) == (*pos).first);
    Assert(cps.apply((*pos).second) == (*pos).second);
  }
#endif /* CVC5_ASSERTIONS */

  // Resize the learnt
  Trace("non-clausal-simplify")
      << "Resize non-clausal learned literals to " << j << std::endl;
  learned_literals.resize(j);

  std::unordered_set<TNode> s;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node assertion = (*assertionsToPreprocess)[i];
    Trace("non-clausal-simplify") << "assertion = " << assertion << std::endl;
    TrustNode assertionNew = newSubstitutions->applyTrusted(assertion, rw);
    if (!assertionNew.isNull())
    {
      Trace("non-clausal-simplify")
          << "assertionNew = " << assertionNew.getNode() << std::endl;
      assertionsToPreprocess->replaceTrusted(i, assertionNew);
      assertion = assertionNew.getNode();
      Assert(rewrite(assertion) == assertion);
    }
    for (;;)
    {
      assertionNew = constantPropagations->applyTrusted(assertion, rw);
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

  // If necessary, add as assertions if needed (when incremental). This is
  // necessary because certain variables cannot truly be eliminated when
  // we are in incremental mode. For example, say our first call to check-sat
  // is a formula F containing variable x. On the second call to check-sat,
  // say we solve a top-level assertion (= x t). Since the solver already has
  // constraints involving x, we must still keep (= x t) as an assertion.
  // However, notice that we do not retract the substitution { x -> t }. This
  // means that all *subsequent* assertions after (= x t) will replace x by t.
  if (assertionsToPreprocess->storeSubstsInAsserts())
  {
    for (const std::pair<const Node, const Node>& pos: nss)
    {
      Node lhs = pos.first;
      // If using incremental, we must check whether this variable has occurred
      // before now. If it has, we must add as an assertion.
      if (d_preprocContext->getSymsInAssertions().contains(lhs))
      {
        // if it has, the substitution becomes an assertion
        TrustNode trhs = newSubstitutions->applyTrusted(lhs, rw);
        Assert(!trhs.isNull());
        Trace("non-clausal-simplify")
            << "substitute: will notify SAT layer of substitution: "
            << trhs.getProven() << std::endl;
        assertionsToPreprocess->addSubstitutionNode(trhs.getProven(),
                                                    trhs.getGenerator());
      }
    }
  }

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
  d_preprocContext->addSubstitutions(*newSubstitutions.get());

  if (!learnedLitsToConjoin.empty())
  {
    size_t replIndex = assertionsToPreprocess->size() - 1;
    Node newConj = nm->mkAnd(learnedLitsToConjoin);
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

  // Note that typically ttls.apply(assert)==assert here.
  // However, this invariant is invalidated for cases where we use explicit
  // equality assertions for variables solved in incremental mode that already
  // exist in assertions, as described above.

  return PreprocessingPassResult::NO_CONFLICT;
}

bool NonClausalSimp::isProofEnabled() const
{
  return options().smt.produceProofs;
}

Node NonClausalSimp::processLearnedLit(Node lit,
                                       theory::TrustSubstitutionMap* subs,
                                       theory::TrustSubstitutionMap* cp)
{
  Rewriter* rw = d_env.getRewriter();
  TrustNode tlit;
  if (subs != nullptr)
  {
    tlit = subs->applyTrusted(lit, rw);
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
      tlit = cp->applyTrusted(lit, rw);
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

Node NonClausalSimp::processRewrittenLearnedLit(TrustNode trn)
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
}  // namespace cvc5::internal
