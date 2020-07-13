/*********************                                                        */
/*! \file abduction_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for abduction queries
 **/

#include "smt/abduction_solver.h"

#include "smt/smt_engine.h"

namespace CVC4 {
namespace smt {
  
AbductionSolver::AbductionSolver(SmtEngine * parent) : d_parent(parent)
{
  
}

AbductionSolver::~AbductionSolver()
{
  
}
bool AbductionSolver::getAbduct(const Node& conj, const TypeNode& grammarType, Node& abd)
{
if (!options::produceAbducts())
  {
    const char* msg = "Cannot get abduct when produce-abducts options is off.";
    throw ModalException(msg);
  }
  Trace("sygus-abduct") << "SmtEngine::getAbduct: conjecture " << conj
                        << std::endl;
  std::vector<Expr> easserts = getExpandedAssertions();
  std::vector<Node> axioms;
  for (unsigned i = 0, size = easserts.size(); i < size; i++)
  {
    axioms.push_back(Node::fromExpr(easserts[i]));
  }
  std::vector<Node> asserts(axioms.begin(), axioms.end());
  // must expand definitions
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  conj = d_private->getProcessAssertions()->expandDefinitions(conj, cache);
  // now negate
  conj = conj.negate();
  d_abdConj = conj;
  asserts.push_back(conj);
  std::string name("A");
  Node aconj = theory::quantifiers::SygusAbduct::mkAbductionConjecture(
      name, asserts, axioms,grammarType);
  // should be a quantified conjecture with one function-to-synthesize
  Assert(aconj.getKind() == kind::FORALL && aconj[0].getNumChildren() == 1);
  // remember the abduct-to-synthesize
  d_sssf = aconj[0][0].toExpr();
  Trace("sygus-abduct") << "SmtEngine::getAbduct: made conjecture : " << aconj
                        << ", solving for " << d_sssf << std::endl;
  // we generate a new smt engine to do the abduction query
  d_subsolver.reset(
      new SmtEngine(NodeManager::currentNM()->toExprManager(), &d_options));
  d_subsolver->setIsInternalSubsolver();
  // get the logic
  LogicInfo l = d_logic.getUnlockedCopy();
  // enable everything needed for sygus
  l.enableSygus();
  d_subsolver->setLogic(l);
  // assert the abduction query
  d_subsolver->assertFormula(aconj.toExpr());
  if (getAbductInternal(abd))
  {
    // successfully generated an abduct, update to abduct state
    d_smtMode = SMT_MODE_ABDUCT;
    return true;
  }
  // failed, we revert to the assert state
  d_smtMode = SMT_MODE_ASSERT;
  return false;
}

bool AbductionSolver::getAbduct(const Node& conj, Node& abd)
{
  TypeNode grammarType;
  return getAbduct(conj, grammarType, abd);
}

bool AbductionSolver::getAbductInternal(Node& abd)
{
  // should have initialized the subsolver by now
  Assert(d_subsolver != nullptr);
  Trace("sygus-abduct") << "  SmtEngine::getAbduct check sat..." << std::endl;
  Result r = d_subsolver->checkSat();
  Trace("sygus-abduct") << "  SmtEngine::getAbduct result: " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    // get the synthesis solution
    std::map<Expr, Expr> sols;
    d_subsolver->getSynthSolutions(sols);
    Assert(sols.size() == 1);
    std::map<Expr, Expr>::iterator its = sols.find(d_sssf);
    if (its != sols.end())
    {
      Trace("sygus-abduct")
          << "SmtEngine::getAbduct: solution is " << its->second << std::endl;
      abd = Node::fromExpr(its->second);
      if (abd.getKind() == kind::LAMBDA)
      {
        abd = abd[1];
      }
      // get the grammar type for the abduct
      Node af = Node::fromExpr(d_sssf);
      Node agdtbv = af.getAttribute(theory::SygusSynthFunVarListAttribute());
      Assert(!agdtbv.isNull());
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
      abd =
          abd.substitute(vars.begin(), vars.end(), syms.begin(), syms.end());

      // if check abducts option is set, we check the correctness
      if (options::checkAbducts())
      {
        checkAbduct(abd);
      }
      return true;
    }
    Trace("sygus-abduct") << "SmtEngine::getAbduct: could not find solution!"
                          << std::endl;
    throw RecoverableModalException("Could not find solution for get-abduct.");
  }
  return false;
}

void AbductionSolver::checkAbduct(Node a)
{
  Assert(a.getType().isBoolean());
  Trace("check-abduct") << "SmtEngine::checkAbduct: get expanded assertions"
                        << std::endl;

  std::vector<Expr> asserts = d_parent->getExpandedAssertions();
  asserts.push_back(a);

  // two checks: first, consistent with assertions, second, implies negated goal
  // is unsatisfiable.
  for (unsigned j = 0; j < 2; j++)
  {
    Trace("check-abduct") << "SmtEngine::checkAbduct: phase " << j
                          << ": make new SMT engine" << std::endl;
    // Start new SMT engine to check solution
    SmtEngine abdChecker(d_exprManager, &d_options);
    abdChecker.setIsInternalSubsolver();
    abdChecker.setLogic(getLogicInfo());
    Trace("check-abduct") << "SmtEngine::checkAbduct: phase " << j
                          << ": asserting formulas" << std::endl;
    for (const Expr& e : asserts)
    {
      abdChecker.assertFormula(e);
    }
    Trace("check-abduct") << "SmtEngine::checkAbduct: phase " << j
                          << ": check the assertions" << std::endl;
    Result r = abdChecker.checkSat();
    Trace("check-abduct") << "SmtEngine::checkAbduct: phase " << j
                          << ": result is " << r << endl;
    std::stringstream serr;
    bool isError = false;
    if (j == 0)
    {
      if (r.asSatisfiabilityResult().isSat() != Result::SAT)
      {
        isError = true;
        serr << "SmtEngine::checkAbduct(): produced solution cannot be shown "
                "to be consisconsistenttent with assertions, result was "
             << r;
      }
      Trace("check-abduct")
          << "SmtEngine::checkAbduct: goal is " << d_abdConj << std::endl;
      // add the goal to the set of assertions
      Assert(!d_abdConj.isNull());
      asserts.push_back(d_abdConj.toExpr());
    }
    else
    {
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        isError = true;
        serr << "SmtEngine::checkAbduct(): negated goal cannot be shown "
                "unsatisfiable with produced solution, result was "
             << r;
      }
    }
    // did we get an unexpected result?
    if (isError)
    {
      InternalError() << serr.str();
    }
  }
}


}/* smt namespace */
}/* CVC4 namespace */
