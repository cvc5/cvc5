/*********************                                                        */
/*! \file non_clausal_simp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Non-clausal simplification preprocessing pass.
 **
 ** Run the nonclausal solver and try to solve all assigned theory literals.
 **/

#include "preprocessing/passes/non_clausal_simp.h"

#include <vector>

#include "base/map_util.h"
#include "context/cdo.h"
#include "options/proof_options.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "proof/proof_manager.h"
#include "prop/cnf_stream.h"
#include "prop/registrar.h"
#include "prop/sat_solver_factory.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_model.h"

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

NonClausalSimp::Statistics::Statistics()
    : d_numConstantProps(
          "preprocessing::passes::NonClausalSimp::NumConstantProps", 0),
      d_cnfTranslateTime(
          "preprocessing::passes::NonClausalSimp::CnfTranslateTime")
{
  smtStatisticsRegistry()->registerStat(&d_numConstantProps);
  smtStatisticsRegistry()->registerStat(&d_cnfTranslateTime);
}

NonClausalSimp::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numConstantProps);
  smtStatisticsRegistry()->unregisterStat(&d_cnfTranslateTime);
}

/* -------------------------------------------------------------------------- */

NonClausalSimp::NonClausalSimp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "non-clausal-simp")
{
}

PreprocessingPassResult NonClausalSimp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());

  d_preprocContext->spendResource(options::preprocessStep());
  unsigned substs_index = d_preprocContext->getSubstitutionsIndex();
  bool noconflict;
  std::vector<Node> learned_literals;

  if (options::skeletonPreprocessing()){
    // solve the boolean skeleton using cryptominisat
    std::tie(noconflict, learned_literals) =
        preprocessByCryptoMinisat(assertionsToPreprocess, substs_index);
  }
  else
  {
    // default
    // solve the boolean skeleton using circuit propagator
    std::tie(noconflict, learned_literals) =
        preprocessByCircuitPropagator(assertionsToPreprocess, substs_index);
  }

  if (!noconflict)
  {
    Trace("non-clausal-simplify")
        << "conflict in non-clausal propagation" << std::endl;
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    assertionsToPreprocess->clear();
    Node n = NodeManager::currentNM()->mkConst<bool>(false);
    assertionsToPreprocess->push_back(n);
    PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
    return PreprocessingPassResult::CONFLICT;
  }

  Trace("non-clausal-simplify") << "Iterate through " << learned_literals.size()
                                << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  SubstitutionMap& top_level_substs =
      d_preprocContext->getTopLevelSubstitutions();
  SubstitutionMap constantPropagations(d_preprocContext->getUserContext());
  SubstitutionMap newSubstitutions(d_preprocContext->getUserContext());
  SubstitutionMap::iterator pos;
  size_t j = 0;
  for (size_t i = 0, size = learned_literals.size(); i < size; ++i)
  {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = learned_literals[i];
    Assert(Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Assert(top_level_substs.apply(learnedLiteral) == learnedLiteral);
    Trace("non-clausal-simplify")
        << "Process learnedLiteral : " << learnedLiteral << std::endl;
    Node learnedLiteralNew = newSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew)
    {
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("non-clausal-simplify")
        << "Process learnedLiteral, after newSubs : " << learnedLiteral
        << std::endl;
    for (;;)
    {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral)
      {
        break;
      }
      d_statistics.d_numConstantProps += 1;
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
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
            << "conflict with " << learned_literals[i] << std::endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        Node n = NodeManager::currentNM()->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n);
        PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
        return PreprocessingPassResult::CONFLICT;
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("non-clausal-simplify") << "solving " << learnedLiteral << std::endl;

    Theory::PPAssertStatus solveStatus =
        d_preprocContext->getTheoryEngine()->solve(learnedLiteral,
                                                   newSubstitutions);

    switch (solveStatus)
    {
      case Theory::PP_ASSERT_STATUS_SOLVED:
      {
        // The literal should rewrite to true
        Trace("non-clausal-simplify")
            << "solved " << learnedLiteral << std::endl;
        Assert(Rewriter::rewrite(newSubstitutions.apply(learnedLiteral))
                   .isConst());
        //        vector<pair<Node, Node> > equations;
        //        constantPropagations.simplifyLHS(top_level_substs,
        //        equations, true); if (equations.empty()) {
        //          break;
        //        }
        //        Assert(equations[0].first.isConst() &&
        //        equations[0].second.isConst() && equations[0].first !=
        //        equations[0].second);
        // else fall through
        break;
      }
      case Theory::PP_ASSERT_STATUS_CONFLICT:
      {
        // If in conflict, we return false
        Trace("non-clausal-simplify")
            << "conflict while solving " << learnedLiteral << std::endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        Node n = NodeManager::currentNM()->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n);
        PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
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
          Assert(constantPropagations.apply(t) == t);
          Assert(top_level_substs.apply(t) == t);
          Assert(newSubstitutions.apply(t) == t);
          constantPropagations.addSubstitution(t, c);
          // vector<pair<Node,Node> > equations;
          // constantPropagations.simplifyLHS(t, c, equations, true);
          // if (!equations.empty()) {
          //   Assert(equations[0].first.isConst() &&
          //   equations[0].second.isConst() && equations[0].first !=
          //   equations[0].second); assertionsToPreprocess->clear();
          //   Node n = NodeManager::currentNM()->mkConst<bool>(false);
          //   assertionsToPreprocess->push_back(n);
          //   PROOF(ProofManager::currentPM()->addDependence(n,
          //   Node::null())); false); return;
          // }
          // top_level_substs.simplifyRHS(constantPropagations);
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
  for (pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos)
  {
    Assert((*pos).first.isVar());
    Assert(top_level_substs.apply((*pos).first) == (*pos).first);
    Assert(top_level_substs.apply((*pos).second) == (*pos).second);
    Assert(newSubstitutions.apply(newSubstitutions.apply((*pos).second))
           == newSubstitutions.apply((*pos).second));
  }
  for (pos = constantPropagations.begin(); pos != constantPropagations.end();
       ++pos)
  {
    Assert((*pos).second.isConst());
    Assert(Rewriter::rewrite((*pos).first) == (*pos).first);
    // Node newLeft = top_level_substs.apply((*pos).first);
    // if (newLeft != (*pos).first) {
    //   newLeft = Rewriter::rewrite(newLeft);
    //   Assert(newLeft == (*pos).second ||
    //          (constantPropagations.hasSubstitution(newLeft) &&
    //          constantPropagations.apply(newLeft) == (*pos).second));
    // }
    // newLeft = constantPropagations.apply((*pos).first);
    // if (newLeft != (*pos).first) {
    //   newLeft = Rewriter::rewrite(newLeft);
    //   Assert(newLeft == (*pos).second ||
    //          (constantPropagations.hasSubstitution(newLeft) &&
    //          constantPropagations.apply(newLeft) == (*pos).second));
    // }
    Assert(constantPropagations.apply((*pos).second) == (*pos).second);
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
    Node assertionNew = newSubstitutions.apply(assertion);
    Trace("non-clausal-simplify") << "assertion = " << assertion << std::endl;
    Trace("non-clausal-simplify")
        << "assertionNew = " << assertionNew << std::endl;
    if (assertion != assertionNew)
    {
      assertion = Rewriter::rewrite(assertionNew);
      Trace("non-clausal-simplify")
          << "rewrite(assertion) = " << assertion << std::endl;
    }
    Assert(Rewriter::rewrite(assertion) == assertion);
    for (;;)
    {
      assertionNew = constantPropagations.apply(assertion);
      if (assertionNew == assertion)
      {
        break;
      }
      d_statistics.d_numConstantProps += 1;
      Trace("non-clausal-simplify")
          << "assertionNew = " << assertionNew << std::endl;
      assertion = Rewriter::rewrite(assertionNew);
      Trace("non-clausal-simplify")
          << "assertionNew = " << assertionNew << std::endl;
    }
    s.insert(assertion);
    assertionsToPreprocess->replace(i, assertion);
    Trace("non-clausal-simplify")
        << "non-clausal preprocessed: " << assertion << std::endl;
  }

  // add substitutions to model, or as assertions if needed (when incremental)
  TheoryModel* m = d_preprocContext->getTheoryEngine()->getModel();
  Assert(m != nullptr);
  NodeManager* nm = NodeManager::currentNM();
  NodeBuilder<> substitutionsBuilder(kind::AND);
  for (pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos)
  {
    Node lhs = (*pos).first;
    Node rhs = newSubstitutions.apply((*pos).second);
    // If using incremental, we must check whether this variable has occurred
    // before now. If it hasn't we can add this as a substitution.
    if (substs_index == 0
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
      substitutionsBuilder << eq;
    }
  }
  // add to the last assertion if necessary
  if (substitutionsBuilder.getNumChildren() > 0)
  {
    substitutionsBuilder << (*assertionsToPreprocess)[substs_index];
    assertionsToPreprocess->replace(
        substs_index, Rewriter::rewrite(Node(substitutionsBuilder)));
  }

  NodeBuilder<> learnedBuilder(kind::AND);
  Assert(assertionsToPreprocess->getRealAssertionsEnd()
         <= assertionsToPreprocess->size());
  learnedBuilder << (*assertionsToPreprocess)
          [assertionsToPreprocess->getRealAssertionsEnd() - 1];

  for (size_t i = 0; i < learned_literals.size(); ++i)
  {
    Node learned = learned_literals[i];
    Assert(top_level_substs.apply(learned) == learned);
    Node learnedNew = newSubstitutions.apply(learned);
    if (learned != learnedNew)
    {
      learned = Rewriter::rewrite(learnedNew);
    }
    Assert(Rewriter::rewrite(learned) == learned);
    for (;;)
    {
      learnedNew = constantPropagations.apply(learned);
      if (learnedNew == learned)
      {
        break;
      }
      d_statistics.d_numConstantProps += 1;
      learned = Rewriter::rewrite(learnedNew);
    }
    if (s.find(learned) != s.end())
    {
      continue;
    }
    s.insert(learned);
    learnedBuilder << learned;
    Trace("non-clausal-simplify")
        << "non-clausal learned : " << learned << std::endl;
  }
  learned_literals.clear();

  for (pos = constantPropagations.begin(); pos != constantPropagations.end();
       ++pos)
  {
    Node cProp = (*pos).first.eqNode((*pos).second);
    Assert(top_level_substs.apply(cProp) == cProp);
    Node cPropNew = newSubstitutions.apply(cProp);
    if (cProp != cPropNew)
    {
      cProp = Rewriter::rewrite(cPropNew);
      Assert(Rewriter::rewrite(cProp) == cProp);
    }
    if (s.find(cProp) != s.end())
    {
      continue;
    }
    s.insert(cProp);
    learnedBuilder << cProp;
    Trace("non-clausal-simplify")
        << "non-clausal constant propagation : " << cProp << std::endl;
  }

  // Add new substitutions to topLevelSubstitutions
  // Note that we don't have to keep rhs's in full solved form
  // because SubstitutionMap::apply does a fixed-point iteration when
  // substituting
  top_level_substs.addSubstitutions(newSubstitutions);

  if (learnedBuilder.getNumChildren() > 1)
  {
    assertionsToPreprocess->replace(
        assertionsToPreprocess->getRealAssertionsEnd() - 1,
        Rewriter::rewrite(Node(learnedBuilder)));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}  // namespace passes

std::pair<bool, std::vector<Node>> NonClausalSimp::preprocessByCryptoMinisat(
    AssertionPipeline* assertionsToPreprocess, unsigned substs_index)
{
  std::unique_ptr<SatSolver> satSolver(SatSolverFactory::createCryptoMinisat(
      smtStatisticsRegistry(), "non_clausal_simp_solver"));
  CVC4::prop::NullRegistrar registrar;
  context::Context context;
  CVC4::prop::TseitinCnfStream cnfStream(satSolver.get(),
                                         &registrar,
                                         &context,
                                         true,
                                         "toCNF-skeleton-preprocessing");
  std::vector<Node> learned_literals;
  Trace("non-clausal-simplify") << "asserting to sat solver" << std::endl;
  {  // for timing
    TimerStat::CodeTimer timer(d_statistics.d_cnfTranslateTime);
    for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
    {
      Assert(Rewriter::rewrite((*assertionsToPreprocess)[i])
             == (*assertionsToPreprocess)[i]);
      // Don't reprocess substitutions
      if (substs_index > 0 && i == substs_index)
      {
        continue;
      }
      Trace("non-clausal-simplify")
          << "asserting " << (*assertionsToPreprocess)[i] << std::endl;
      cnfStream.convertAndAssert(
          (*assertionsToPreprocess)[i], false, false, RULE_GIVEN);
    }
  } // end timing
  Trace("non-clausal-simplify") << "solving" << std::endl;
  if (satSolver->solve() == SAT_VALUE_FALSE)
  {
    // If in conflict, just return false
    return std::make_pair(false, learned_literals);
  }

  std::vector<SatLiteral> topLevelUnits = satSolver->getTopLevelUnits();
  for (size_t i = 0; i < topLevelUnits.size(); i++)
  {
    SatLiteral lit = topLevelUnits[i];
    if (const TNode* learnedLiteral = FindOrNull(cnfStream.getNodeCache(), lit))
    {
      // If the learned literal is not created internally by cryptominisat
      learned_literals.push_back(*learnedLiteral);
    }
  }
  return std::make_pair(true, learned_literals);
}

std::pair<bool, std::vector<Node>>
NonClausalSimp::preprocessByCircuitPropagator(
    AssertionPipeline* assertionsToPreprocess, unsigned substs_index)
{
  theory::booleans::CircuitPropagator* propagator =
      d_preprocContext->getCircuitPropagator();
  std::vector<Node> learned_literals;
  if (propagator->getNeedsFinish())
  {
    propagator->finish();
    propagator->setNeedsFinish(false);
  }
  propagator->initialize();

  // Assert all the assertions to the propagator
  Trace("non-clausal-simplify") << "asserting to propagator" << std::endl;
  {  // for timing
    TimerStat::CodeTimer timer(d_statistics.d_cnfTranslateTime);
    for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
    {
      Assert(Rewriter::rewrite((*assertionsToPreprocess)[i])
             == (*assertionsToPreprocess)[i]);
      // Don't reprocess substitutions
      if (substs_index > 0 && i == substs_index)
      {
        continue;
      }
      Trace("non-clausal-simplify")
          << "asserting " << (*assertionsToPreprocess)[i] << std::endl;
      Debug("cores") << "propagator->assertTrue: " << (*assertionsToPreprocess)[i]
                     << std::endl;
      propagator->assertTrue((*assertionsToPreprocess)[i]);
    }
  }  // end timing
  Trace("non-clausal-simplify") << "propagating" << std::endl;
  if (propagator->propagate())
  {
    // If in conflict, just return false
    propagator->setNeedsFinish(true);
    return std::make_pair(false, learned_literals);
  }
  learned_literals = propagator->getLearnedLiterals();
  propagator->setNeedsFinish(true);
  return std::make_pair(true, learned_literals);
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
