/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for abduction queries.
 */

#include "smt/abduction_solver.h"

#include <sstream>

#include "base/modal_exception.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "smt/sygus_solver.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_abduct.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

AbductionSolver::AbductionSolver(Env& env) : EnvObj(env) {}

AbductionSolver::~AbductionSolver() {}
bool AbductionSolver::getAbduct(const std::vector<Node>& axioms,
                                const Node& goal,
                                const TypeNode& grammarType,
                                Node& abd)
{
  if (!options().smt.produceAbducts)
  {
    const char* msg = "Cannot get abduct when produce-abducts options is off.";
    throw ModalException(msg);
  }
  Trace("sygus-abduct") << "Axioms: " << axioms << std::endl;
  Trace("sygus-abduct") << "SolverEngine::getAbduct: goal " << goal
                        << std::endl;
  std::vector<Node> asserts(axioms.begin(), axioms.end());
  // must expand definitions
  Node conjn = d_env.getTopLevelSubstitutions().apply(goal);
  conjn = rewrite(conjn);
  // now negate
  conjn = conjn.negate();
  d_abdConj = conjn;
  asserts.push_back(conjn);
  std::string name("__internal_abduct");
  Node aconj = quantifiers::SygusAbduct::mkAbductionConjecture(
      name, asserts, axioms, grammarType);
  // should be a quantified conjecture with one function-to-synthesize
  Assert(aconj.getKind() == kind::FORALL && aconj[0].getNumChildren() == 1);
  // remember the abduct-to-synthesize
  d_sssf = aconj[0][0];
  Trace("sygus-abduct") << "SolverEngine::getAbduct: made conjecture : "
                        << aconj << ", solving for " << d_sssf << std::endl;

  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.writeQuantifiers().sygus = true;
  // by default, we don't want disjunctive terms (ITE, OR) in abducts
  if (!d_env.getOptions().quantifiers.sygusGrammarUseDisjWasSetByUser)
  {
    subOptions.writeQuantifiers().sygusGrammarUseDisj = false;
  }
  SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  // we generate a new smt engine to do the abduction query
  initializeSubsolver(d_subsolver, ssi);
  // get the logic
  LogicInfo l = d_subsolver->getLogicInfo().getUnlockedCopy();
  // enable everything needed for sygus
  l.enableSygus();
  d_subsolver->setLogic(l);
  // assert the abduction query
  d_subsolver->assertFormula(aconj);
  d_axioms = axioms;
  return getAbductInternal(abd);
}

bool AbductionSolver::getAbductNext(Node& abd)
{
  // Since we are using the subsolver's check-sat interface directly, we
  // simply call getAbductInternal again here. We assert that the subsolver
  // is already initialized, which must be the case or else we are not in the
  // proper SMT mode to make this call. Due to the default behavior of
  // subsolvers having synthesis conjectures, this is guaranteed to produce
  // a new solution.
  Assert(d_subsolver != nullptr);
  return getAbductInternal(abd);
}

bool AbductionSolver::getAbductInternal(Node& abd)
{
  // should have initialized the subsolver by now
  Assert(d_subsolver != nullptr);
  Trace("sygus-abduct") << "  SolverEngine::getAbduct check sat..."
                        << std::endl;
  Result r = d_subsolver->checkSat();
  Trace("sygus-abduct") << "  SolverEngine::getAbduct result: " << r
                        << std::endl;
  // get the synthesis solution
  std::map<Node, Node> sols;
  // use the "getSubsolverSynthSolutions" interface, since we asserted the
  // internal form of the SyGuS conjecture and used check-sat.
  if (d_subsolver->getSubsolverSynthSolutions(sols))
  {
    Assert(sols.size() == 1);
    std::map<Node, Node>::iterator its = sols.find(d_sssf);
    if (its != sols.end())
    {
      Trace("sygus-abduct") << "SolverEngine::getAbduct: solution is "
                            << its->second << std::endl;
      abd = its->second;
      if (abd.getKind() == kind::LAMBDA)
      {
        abd = abd[1];
      }
      // get the grammar type for the abduct
      Node agdtbv =
          theory::quantifiers::SygusUtils::getOrMkSygusArgumentList(d_sssf);
      if(!agdtbv.isNull())
      {
        Assert(agdtbv.getKind() == kind::BOUND_VAR_LIST);
        // convert back to original
        // must replace formal arguments of abd with the free variables in the
        // input problem that they correspond to.
        std::vector<Node> vars;
        std::vector<Node> syms;
        SygusVarToTermAttribute sta;
        for (const Node& bv : agdtbv)
        {
          vars.push_back(bv);
          syms.push_back(bv.hasAttribute(sta) ? bv.getAttribute(sta) : bv);
        }
        abd = abd.substitute(vars.begin(), vars.end(), syms.begin(), syms.end());
      }

      // if check abducts option is set, we check the correctness
      if (options().smt.checkAbducts)
      {
        checkAbduct(abd);
      }
      return true;
    }
    Trace("sygus-abduct") << "SolverEngine::getAbduct: could not find solution!"
                          << std::endl;
    throw RecoverableModalException("Could not find solution for get-abduct.");
  }
  return false;
}

void AbductionSolver::checkAbduct(Node a)
{
  Assert(a.getType().isBoolean());
  Trace("check-abduct") << "SolverEngine::checkAbduct: get expanded assertions"
                        << std::endl;
  bool canTrustResult = SygusSolver::canTrustSynthesisResult(options());
  if (!canTrustResult)
  {
    warning() << "Running check-abducts is not guaranteed to pass with the "
                 "current options."
              << std::endl;
  }
  std::vector<Node> asserts(d_axioms.begin(), d_axioms.end());
  asserts.push_back(a);

  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.writeSmt().produceAbducts = false;
  SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  // two checks: first, consistent with assertions, second, implies negated goal
  // is unsatisfiable.
  for (unsigned j = 0; j < 2; j++)
  {
    Trace("check-abduct") << "SolverEngine::checkAbduct: phase " << j
                          << ": make new SMT engine" << std::endl;
    // Start new SMT engine to check solution
    std::unique_ptr<SolverEngine> abdChecker;
    initializeSubsolver(abdChecker, ssi);
    Trace("check-abduct") << "SolverEngine::checkAbduct: phase " << j
                          << ": asserting formulas" << std::endl;
    for (const Node& e : asserts)
    {
      abdChecker->assertFormula(e);
    }
    Trace("check-abduct") << "SolverEngine::checkAbduct: phase " << j
                          << ": check the assertions" << std::endl;
    Result r = abdChecker->checkSat();
    Trace("check-abduct") << "SolverEngine::checkAbduct: phase " << j
                          << ": result is " << r << std::endl;
    std::stringstream serr;
    bool isError = false;
    bool hardFailure = canTrustResult;
    if (j == 0)
    {
      if (r.getStatus() != Result::SAT)
      {
        isError = true;
        serr
            << "SolverEngine::checkAbduct(): produced solution cannot be shown "
               "to be consistent with assertions, result was "
            << r;
        hardFailure = r.isUnknown() ? false : hardFailure;
      }
      Trace("check-abduct")
          << "SolverEngine::checkAbduct: goal is " << d_abdConj << std::endl;
      // add the goal to the set of assertions
      Assert(!d_abdConj.isNull());
      asserts.push_back(d_abdConj);
    }
    else
    {
      if (r.getStatus() != Result::UNSAT)
      {
        isError = true;
        serr << "SolverEngine::checkAbduct(): negated goal cannot be shown "
                "unsatisfiable with produced solution, result was "
             << r;
        hardFailure = r.isUnknown() ? false : hardFailure;
      }
    }
    // did we get an unexpected result?
    if (isError)
    {
      if (hardFailure)
      {
        InternalError() << serr.str();
      }
      else
      {
        warning() << serr.str() << std::endl;
      }
    }
  }
}

}  // namespace smt
}  // namespace cvc5::internal
