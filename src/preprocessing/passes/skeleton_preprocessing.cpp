/*********************                                                        */
/*! \file skeleton_preprocessing.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Haoze Wu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Boolean skeleton preprocessing pass.
 **
 ** Run cryptominisat and try to solve all assigned theory literals.
 **/

 #include "preprocessing/passes/skeleton_preprocessing.h"

 #ifdef CVC4_USE_CRYPTOMINISAT
 #include <cryptominisat5/cryptominisat.h>
 #endif

 #include "prop/registrar.h"
 #include "prop/cnf_stream.h"
 #include "prop/sat_solver_factory.h"

 #include "proof/proof_manager.h"

 #include "context/cdo.h"
 #include "options/proof_options.h"
 #include "smt/smt_statistics_registry.h"
 #include "theory/theory_model.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {


/* -------------------------------------------------------------------------- */

SkeletonPreprocessing::SkeletonPreprocessing(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "non-clausal-simp-sat")
{
}

PreprocessingPassResult SkeletonPreprocessing::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{

  Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());

  d_preprocContext->spendResource(options::preprocessStep());


  // Convert the original formula into a boolean formula and solve it
  // with cryptominisat
  SatSolver* d_satSolver = SatSolverFactory::createCryptoMinisat(smtStatisticsRegistry(), "non_clausal_simp_solver");
  CVC4::prop::NullRegistrar d_registrar;
  context::Context d_context;
  CVC4::prop::TseitinCnfStream d_cnfStream (d_satSolver, &d_registrar,
                                            &d_context, true,
                                            "toCNF-skeleton-preprocessing");

  Trace("skeleton-preprocessing") << "asserting to sat solver" << std::endl;

  unsigned substs_index = d_preprocContext->getSubstitutionsIndex();
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Assert(Rewriter::rewrite((*assertionsToPreprocess)[i])
              == (*assertionsToPreprocess)[i]);
       // Don't reprocess substitutions
       if (substs_index > 0 && i == substs_index)
       {
         continue;
       }
       Trace("skeleton-preprocessing")
           << "asserting " << (*assertionsToPreprocess)[i] << std::endl;
       d_cnfStream.convertAndAssert((*assertionsToPreprocess)[i], false, false,
                                    RULE_GIVEN);
  }



  SatValue result = d_satSolver->solve();

  if (result==SAT_VALUE_FALSE){
    // If in conflict, just return false
    Trace("skeleton-preprocessing")
        << "conflict in non-clausal propagation" << std::endl;
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    assertionsToPreprocess->clear();
    Node n = NodeManager::currentNM()->mkConst<bool>(false);
    assertionsToPreprocess->push_back(n);
    PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
    delete d_satSolver;
    return PreprocessingPassResult::CONFLICT;
  }

  std::vector<SatLiteral> topLevelUnits = d_satSolver->getTopLevelUnits();

  std::vector<TNode> learned_literals;


  for (size_t i = 0; i < topLevelUnits.size(); i++){
    SatLiteral lit = topLevelUnits[i];
    if (d_cnfStream.getNodeCache().find(lit)
        != d_cnfStream.getNodeCache().end()) {
      // if the literal is in the getNodeCache
      Node learnedLiteral = Rewriter::rewrite(d_cnfStream.getNode(lit));
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
          Trace("skeleton-preprocessing")
              << "conflict with " << learned_literals[i] << std::endl;
          Assert(!options::unsatCores());
          assertionsToPreprocess->clear();
          Node n = NodeManager::currentNM()->mkConst<bool>(false);
          assertionsToPreprocess->push_back(n);
          PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
          delete d_satSolver;
          return PreprocessingPassResult::CONFLICT;
        }
      }
      learned_literals.push_back(learnedLiteral);
    }
  }


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
    Trace("skeleton-preprocessing")
        << "Process learnedLiteral : " << learnedLiteral << std::endl;
    Node learnedLiteralNew = newSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew)
    {
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("skeleton-preprocessing")
        << "Process learnedLiteral, after newSubs : " << learnedLiteral
        << std::endl;
    for (;;)
    {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral)
      {
        break;
      }
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("skeleton-preprocessing")
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
        Trace("skeleton-preprocessing")
            << "conflict with " << learned_literals[i] << std::endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        Node n = NodeManager::currentNM()->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n);
        PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
        delete d_satSolver;
        return PreprocessingPassResult::CONFLICT;
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("skeleton-preprocessing") << "solving " << learnedLiteral << std::endl;

    Theory::PPAssertStatus solveStatus =
        d_preprocContext->getTheoryEngine()->solve(learnedLiteral,
                                                   newSubstitutions);

    switch (solveStatus)
    {
      case Theory::PP_ASSERT_STATUS_SOLVED:
      {
        // The literal should rewrite to true
        Trace("skeleton-preprocessing")
            << "solved " << learnedLiteral << std::endl;
        Assert(Rewriter::rewrite(newSubstitutions.apply(learnedLiteral))
                   .isConst());
        //        vector<pair<Node, Node> > equations;
        //        constantPropagations.simplifyLHS(top_level_substs, equations,
        //        true); if (equations.empty()) {
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
        Trace("skeleton-preprocessing")
            << "conflict while solving " << learnedLiteral << std::endl;
        Assert(!options::unsatCores());
        assertionsToPreprocess->clear();
        Node n = NodeManager::currentNM()->mkConst<bool>(false);
        assertionsToPreprocess->push_back(n);
        PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
        delete d_satSolver;
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
          //   PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
          //   false); return;
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
  Trace("skeleton-preprocessing")
      << "Resize non-clausal learned literals to " << j << std::endl;
  learned_literals.resize(j);

  unordered_set<TNode, TNodeHashFunction> s;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node assertion = (*assertionsToPreprocess)[i];
    Node assertionNew = newSubstitutions.apply(assertion);
    Trace("skeleton-preprocessing") << "assertion = " << assertion << std::endl;
    Trace("skeleton-preprocessing")
        << "assertionNew = " << assertionNew << std::endl;
    if (assertion != assertionNew)
    {
      assertion = Rewriter::rewrite(assertionNew);
      Trace("skeleton-preprocessing")
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
      Trace("skeleton-preprocessing")
          << "assertionNew = " << assertionNew << std::endl;
      assertion = Rewriter::rewrite(assertionNew);
      Trace("skeleton-preprocessing")
          << "assertionNew = " << assertionNew << std::endl;
    }
    s.insert(assertion);
    assertionsToPreprocess->replace(i, assertion);
    Trace("skeleton-preprocessing")
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
      Trace("skeleton-preprocessing")
          << "substitute: " << lhs << " " << rhs << std::endl;
      m->addSubstitution(lhs, rhs);
    }
    else
    {
      // if it has, the substitution becomes an assertion
      Node eq = nm->mkNode(kind::EQUAL, lhs, rhs);
      Trace("skeleton-preprocessing")
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
      learned = Rewriter::rewrite(learnedNew);
    }
    if (s.find(learned) != s.end())
    {
      continue;
    }
    s.insert(learned);
    learnedBuilder << learned;
    Trace("skeleton-preprocessing")
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
    Trace("skeleton-preprocessing")
        << "constant propagation : " << cProp << std::endl;
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

  delete d_satSolver;

  return PreprocessingPassResult::NO_CONFLICT;
}  // namespace passes

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
