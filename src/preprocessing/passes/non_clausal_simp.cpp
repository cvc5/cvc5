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
#include <cryptominisat5/cryptominisat.h>

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

NonClausalSimp::NonClausalSimp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "non-clausal-simp")
{
  //d_satSolver = SatSolverFactory::createCryptoMinisat(smtStatisticsRegistry(), "non_clausal_simp_solver");
}

PreprocessingPassResult NonClausalSimp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());

  d_preprocContext->spendResource(options::preprocessStep());

  SatSolver* d_satSolver = SatSolverFactory::createCryptoMinisat(smtStatisticsRegistry(), "non_clausal_simp_solver");

  context::CDO<unsigned>& substs_index =
      assertionsToPreprocess->getSubstitutionsIndex();
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    if (substs_index > 0 && i == substs_index)
    {
      continue;
    }
    Trace("non-clausal-simplify") << "Assertion #" << i << " : "
                                  << (*assertionsToPreprocess)[i] << std::endl;
  }

  d_preprocContext->spendResource(options::preprocessStep());


  //SatSolver* d_satSolver = prop::SatSolverFactory::createCadical(smtStatisticsRegistry(),
                                                 //"non-clausal-simp");
  //Registrar d_registrar = new CVC4::prop::NullRegistrar();
  CVC4::prop::NullRegistrar d_registrar;
  //context::Context* d_context = new context::Context();
  context::Context d_context;
  //CnfStream* d_cnfStream = new
  CVC4::prop::TseitinCnfStream d_cnfStream (d_satSolver, &d_registrar, &d_context, true, "toCNF-non-clausal");


  Trace("non-clausal-simplify") << "asserting to sat solver" << std::endl;

  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    d_cnfStream.convertAndAssert((*assertionsToPreprocess)[i], false, false, RULE_GIVEN);
  }

  SatValue result = d_satSolver->solve();

  std::vector<SatLiteral> topLevelUnits = d_satSolver->getTopLevelUnits();

  std::vector<TNode> learned_literals;

  for (size_t i = 0; i < topLevelUnits.size(); i++){
    SatLiteral lit = topLevelUnits[i];
    if (d_cnfStream.getNodeCache().find(lit) != d_cnfStream.getNodeCache().end()) {
      // if the literal is in the getNodeCache
      Node learnedLiteral = d_cnfStream.getNode(lit);
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
              << "conflict with " << learnedLiteral << std::endl;
          Assert(!options::unsatCores());
          assertionsToPreprocess->clear();
          Node n = NodeManager::currentNM()->mkConst<bool>(false);
          assertionsToPreprocess->push_back(n);
          PROOF(ProofManager::currentPM()->addDependence(n, Node::null()));
          return PreprocessingPassResult::CONFLICT;
        }
      }
      learned_literals.push_back(learnedLiteral);
    }
  }

  SubstitutionMap& top_level_substs =
      assertionsToPreprocess->getTopLevelSubstitutions();
  SubstitutionMap constantPropagations(d_preprocContext->getUserContext());
  SubstitutionMap newSubstitutions(d_preprocContext->getUserContext());
  SubstitutionMap::iterator pos;
  size_t j = 0;
  for (size_t i = 0, size = learned_literals.size(); i < size; ++i)
  {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = learned_literals[i];
    //Assert(Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    //Assert(top_level_substs.apply(learnedLiteral) == learnedLiteral);
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
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("non-clausal-simplify")
        << "Process learnedLiteral, after constProp : " << learnedLiteral
        << std::endl;


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
    //Assert(Rewriter::rewrite(learned) == learned);
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

  delete d_satSolver;

  if (result==SAT_VALUE_FALSE) return PreprocessingPassResult::CONFLICT;
  return PreprocessingPassResult::NO_CONFLICT;

}  // namespace passes

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
