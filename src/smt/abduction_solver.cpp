/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for abduction queries.
 */

#include "smt/abduction_solver.h"
#include "smt/env.h"
#include "smt/sygus_solver.h"
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
    throw ModalException("Cannot get abduct when produce-abducts options is off.");
  }
  
  std::vector<Node> asserts(axioms.begin(), axioms.end());
  Node conjn = d_env.getTopLevelSubstitutions().apply(goal).negate();
  asserts.push_back(conjn);
  std::string name("__internal_abduct");
  Node aconj = quantifiers::SygusAbduct::mkAbductionConjecture(
      name, asserts, axioms, grammarType);

  Assert(aconj.getKind() == Kind::FORALL && aconj[0].getNumChildren() == 1);
  d_sssf = aconj[0][0];

  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.writeQuantifiers().sygus = true;
  if (!d_env.getOptions().quantifiers.sygusGrammarUseDisjWasSetByUser)
  {
    subOptions.writeQuantifiers().sygusGrammarUseDisj = false;
  }
  SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  initializeSubsolver(d_subsolver, ssi);
  LogicInfo l = d_subsolver->getLogicInfo().getUnlockedCopy().enableSygus();
  d_subsolver->setLogic(l);
  d_subsolver->assertFormula(aconj);
  d_axioms = axioms;
  return getAbductInternal(abd);
}

bool AbductionSolver::getAbductNext(Node& abd)
{
  Assert(d_subsolver != nullptr);
  return getAbductInternal(abd);
}

bool AbductionSolver::getAbductInternal(Node& abd)
{
  Assert(d_subsolver != nullptr);
  Result r = d_subsolver->checkSat();
  std::map<Node, Node> sols;
  if (d_subsolver->getSubsolverSynthSolutions(sols))
  {
    Assert(sols.size() == 1);
    std::map<Node, Node>::iterator its = sols.find(d_sssf);
    if (its != sols.end())
    {
      abd = its->second;
      if (abd.getKind() == Kind::LAMBDA)
      {
        abd = abd[1];
      }
      Node agdtbv =
          theory::quantifiers::SygusUtils::getOrMkSygusArgumentList(d_sssf);
      if(!agdtbv.isNull())
      {
        Assert(agdtbv.getKind() == Kind::BOUND_VAR_LIST);
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

      if (options().smt.checkAbducts)
      {
        checkAbduct(abd);
      }
      return true;
    }
    throw RecoverableModalException("Could not find solution for get-abduct.");
  }
  return false;
}

void AbductionSolver::checkAbduct(Node a)
{
  Assert(a.getType().isBoolean());
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
  for (unsigned j = 0; j < 2; j++)
  {
    std::unique_ptr<SolverEngine> abdChecker;
    initializeSubsolver(abdChecker, ssi);
    for (const Node& e : asserts)
    {
      abdChecker->assertFormula(e);
    }
    Result r = abdChecker->checkSat();
    std::stringstream serr;
    bool isError = false;
    bool hardFailure = canTrustResult;
    if (j == 0)
    {
      if (r.getStatus() != Result::SAT)
      {
        isError = true;
        serr
            << "Produced solution cannot be shown to be consistent with assertions, result was "
            << r;
        hardFailure = r.isUnknown() ? false : hardFailure;
      }
      Assert(!d_abdConj.isNull());
      asserts.push_back(d_abdConj);
    }
    else
    {
      if (r.getStatus() != Result::UNSAT)
      {
        isError = true;
        serr << "Negated goal cannot be shown unsatisfiable with produced solution, result was "
             << r;
        hardFailure = r.isUnknown() ? false : hardFailure;
      }
    }
   
